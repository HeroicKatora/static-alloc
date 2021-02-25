//! Dynamically pin values to the stack.
//!
//! This is motivated by a short-coming of pinning in situations where no global allocator is
//! available (or the use of one is not desired). The usual solution for pinning a value to the
//! stack is by utilizing the `pin_utils` macro, which works by shadowing a value and thus making
//! it impossible to avoid its Drop impl being run. However, by design this can only work if the
//! number of values is statically known.
//!
//! This crate complements the mechanism. It leverages a pinned wrapper around an area of memory to
//! constructs a linked list of values that are dropped together with that region, and thus can be
//! treated as pinned as well. The downside of this is a more imprecise tracking which requires the
//! values themselves to live for the `'static` lifetime by default.
//!
//! # Usage
//!
//! Use this to have subroutines that starts some task that must be pinned while it is running. An
//! example for this is a DMA transfer, that absolutely must signal or wait for the remote end when
//! it is dropped (as otherwise some memory might get corrupted later). This would usually not be
//! easily possible as stack-pinning the tasks within the subroutine would immediately drop them on
//! exit.
//!
//! ```
//! use core::pin::Pin;
//! use exit_stack::ExitStack;
//!
//! #[derive(Default)]
//! struct DmaTask {
//!     // ..
//! # _inner: (),
//! }
//!
//! impl DmaTask {
//!     // Start a DMA transfer, return an identifier for it.
//!     pub fn start(self: Pin<&mut Self>) -> usize {
//!         // ..
//! # 0
//!     }
//! }
//!
//! fn start_pinned(mut stack: Pin<&ExitStack<DmaTask>>) -> Option<usize> {
//!     let task = stack
//!         .slot()?
//!         .pin(DmaTask::default());
//!     Some(task.start())
//! }
//! ```
#![no_std]
use core::cell::Cell;
use core::mem::MaybeUninit;
use core::pin::Pin;
use core::ptr::NonNull;

use static_alloc::leaked::LeakBox;
use static_alloc::unsync::Bump;

/// Provides memory suitable for dynamically stack-allocating pinned values.
///
/// Alternatively, you can also use this as a pre-allocated buffer for pinning values to the heap.
/// The internal implementation guarantees that the stack can allocate _at least one_ value of type
/// `Mem`. Also, there will be no changes that _reduce_ the amount of values in a patch version, it
/// will require require at least a minor version bump.
pub struct ExitStack<Mem> {
    /// Memory, padded to hold _at least_ one slot of `Mem`.
    memory: Bump<PinSlot<Mem>>,
    /// The exit handler to the last filled slot of the exit stack.
    top: Cell<Option<ExitHandle>>,
}

type ExitHandle = NonNull<PinSlot<dyn Drop>>;

/// A stack allocation that one can pin a value into.
///
/// This contains two references: One to uninitialized stack allocated memory large enough to store
/// a value of the requested type into, and another reference to the head of a linked list of
/// pinned values. When the caller decides to fill the slot then it is written to the stack memory
/// and prepended to the linked list such that the value is guaranteed to drop before all other
/// values contained in it.
pub struct Slot<'lt, T> {
    /// The slot which we can fill with a value and meta data.
    value: LeakBox<'lt, MaybeUninit<PinSlot<T>>>,
    /// Where we will commit ourselves to pin the value. If we write a pointer here then it _must_
    /// be dropped before the box's memory is invalidated.
    slotter: &'lt Cell<Option<ExitHandle>>,
}

/// One entry in the exit stack linked list.
///
/// It contains the link to the next entry and a pinned value that must be dropped in-place.
struct PinSlot<T: ?Sized> {
    link: Option<ExitHandle>,
    value: T,
}

impl<Mem> ExitStack<Mem> {
    /// Create an empty exit stack.
    ///
    /// The available memory for the stack is specified by the `Mem` type parameter.
    pub fn new() -> Self {
        ExitStack {
            memory: Bump::uninit(),
            top: Cell::new(None),
        }
    }

    /// Prepare a slot for pinning a value to the stack.
    ///
    /// Note that dropping may be delayed arbitrarily since this method can't control when the
    /// `ExitStack` itself is dropped. Thus the pinned value must not borrow temporary data.
    pub fn slot<'stack, T: 'static>(self: Pin<&'stack Self>)
        -> Option<Slot<'stack, T>>
    {
        let this: &'stack Self = self.get_ref();
        let value = this.memory.bump_box().ok()?;
        Some(Slot {
            slotter: &this.top,
            value,
        })
    }

    /// Infallibly get a slot for the type of the memory, and pin a value.
    ///
    /// This is useful a small utility wrapper if you want to have a small 'stack' that can make
    /// room for a single entry, on demand. All other entries in the exit stack will be popped, and
    /// the memory allocator will be cleared before the new value is pinned.
    ///
    /// You can also use this method to defer dropping of a pinned task beyond your own method's
    /// body.
    ///
    /// # Usage
    ///
    /// ```
    /// use core::pin::Pin;
    /// use exit_stack::ExitStack;
    /// # use core::future::Future;
    /// # use core::task::{Context, Poll};
    ///
    /// // Some async future that is not Unpin.
    /// #[derive(Default)]
    /// struct Task {
    ///     // ..
    /// # _i: core::marker::PhantomPinned,
    /// }
    ///
    /// # impl Future for Task {
    /// #   type Output = u32;
    /// #   fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    /// #     Poll::Ready(0)
    /// #   }
    /// # }
    ///
    /// async fn with_stack(mut stack: Pin<&mut ExitStack<Task>>) {
    ///     stack.as_mut().set(Task::default()).await;
    ///     // Reuse the stack another time.
    ///     // The previous task is dropped.
    ///     stack.as_mut().set(Task::default()).await;
    ///     // Note that the second task still lives when we return.
    /// }
    /// ```
    pub fn set<'stack>(mut self: Pin<&'stack mut Self>, val: Mem)
        -> Pin<&'stack mut Mem>
    where
        Mem: 'static,
    {
        self.as_mut().pop_all();
        // The memory was reset here..
        match self.into_ref().slot() {
            Some(slot) => slot.pin(val),
            None => unreachable!("The memory can allocate at least one slot"),
        }
    }

    /// Drop all values, resetting the stack.
    pub fn pop_all(self: Pin<&mut Self>) {
        unsafe {
            // SAFETY: inner_pop_all_with_unsafe_self_and_pinned will not move a pinned value.
            self.get_unchecked_mut().inner_pop_all_with_unsafe_self_and_pinned()
        }
    }

    fn inner_pop_all_with_unsafe_self_and_pinned(&mut self) {
        // Ensures that, if we panic unwind, the rest continues to be dropped under the threat of aborting.
        struct UnwindFlag {
            chain: Option<ExitHandle>,
        }

        // !!! In case of another panic we _will_ abort, ourselves, not depending on Rust !!!
        impl core::ops::Drop for UnwindFlag {
            fn drop(&mut self) {
                while let Some(exit_handle) = self.chain {
                    // SAFETY: we only store pointers to the same stack here, which is still valid.
                    let slot = unsafe { &mut *exit_handle.as_ptr() };
                    let abort_flag = AbortOnDrop;
                    // SAFETY: fulfilling our pin promise here.
                    // This is also uniquely dropped as it was owned by `self.chain` before.
                    unsafe { core::ptr::drop_in_place(&mut slot.value) };
                    // Oh great, we didn't panic calling this drop. Let's not abort.
                    core::mem::forget(abort_flag);
                    self.chain = slot.link;
                }
            }
        }

        let mut flag = UnwindFlag { chain: self.top.take() };

        while let Some(exit_handle) = flag.chain.take() {
            // SAFETY: we only store pointers to the same stack here, which is still valid.
            let slot = unsafe { &mut *exit_handle.as_ptr() };
            // This is also uniquely dropped as it was owned by `flag.chain` before.
            unsafe { core::ptr::drop_in_place(&mut slot.value) };
            flag.chain = slot.link;
        }

        // No more values are present, feel free to move anything.
        self.memory.reset()
    }
}

impl<'lt, T> Slot<'lt, T> {
    /// Pin a value to the stack.
    ///
    /// Returns the value if there is no more space in the reserved portion of memory to pin the
    /// new value. You might try calling `pop_all` then to free some.
    ///
    /// Note that dropping might be delayed arbitrarily as the ExitStack has no control over its
    /// own drop point, hence values must live for a static duration.
    pub fn pin(self, value: T) -> Pin<&'lt mut T>
    where
        T: 'static
    {
        // Store the old pointer into our linked list.
        let link = self.slotter.get();
        let boxed = LeakBox::write(self.value, PinSlot { link, value });
        // Now round-trip through pointer. Guarantees that the returned value is based on the
        // pointer we store in the exit stack, which is required for provenance reasons.
        // Has Shared-read-write ..
        let pointer = LeakBox::into_raw(boxed);
        // .. so does this shared-read-write.
        let exit_handle: *mut PinSlot<dyn Drop> = pointer;
        // Overwrite the pointer that is dropped first. The old still has a guarantee of being
        // dropped because the ExitStack will iterate over us, guaranteed with this same write as
        // we've set the link to the old pointer.
        self.slotter.set(NonNull::new(exit_handle));
        // .. so this is unique write above these two pointers.
        // Pin is sound because we've registered ourselves in slotter.
        unsafe { Pin::new_unchecked(&mut (*pointer).value) }
    }

    /// Pin a short-lived value to this exit stack.
    ///
    /// # Safety
    ///
    /// The caller guarantees that the exit stack is dropped _before_ the validity of `T` expires.
    #[allow(dead_code)] // Might pub this later.
    pub unsafe fn pin_local(self, value: T) -> Pin<&'lt mut T> {
        // Store the old pointer into our linked list.
        let link = self.slotter.get();
        let boxed = LeakBox::write(self.value, PinSlot { link, value });
        // Now round-trip through pointer. Guarantees that the returned value is based on the
        // pointer we store in the exit stack, which is required for provenance reasons.
        // Has Shared-read-write ..
        let pointer = LeakBox::into_raw(boxed);
        // .. so does this shared-read-write.
        let raw_handle: *mut PinSlot<dyn Drop + 'lt> = pointer;
        // Transmute away the lifetime. This is safe because we will only dereference the handle
        // while the ExitStack is alive or just being dropped, and the caller promised us that it
        // is okay in that lifetime.
        let exit_handle: *mut PinSlot<dyn Drop> = core::mem::transmute(raw_handle);
        // Overwrite the pointer that is dropped first. The old still has a guarantee of being
        // dropped because the ExitStack will iterate over us, guaranteed with this same write as
        // we've set the link to the old pointer.
        self.slotter.set(NonNull::new(exit_handle));
        // .. so this is unique write above these two pointers.
        // Pin is sound because we've registered ourselves in slotter.
        Pin::new_unchecked(&mut (*pointer).value)
    }
}

impl<Mem> core::ops::Drop for ExitStack<Mem> {
    fn drop(&mut self) {
        self.inner_pop_all_with_unsafe_self_and_pinned()
    }
}

/// An object-safe trait for types that are droppable. So, all of them.
trait Drop {}

impl<T: ?Sized> Drop for T {}

// A struct that guarantees that no more execution happens after it is dropped. It must be
// forgotten, a very strong pre-pooping of our pants.
struct AbortOnDrop;
impl core::ops::Drop for AbortOnDrop {
    fn drop(&mut self) {
        struct CauseDoublePanic;
        impl core::ops::Drop for CauseDoublePanic {
            fn drop(&mut self) { panic!() }
        }
        struct FallbackInCaseThisDidntAbort;
        impl core::ops::Drop for FallbackInCaseThisDidntAbort {
            fn drop(&mut self) { loop {} }
        }
        // Since we are no_std.. FIXME: use `cfg(accessible())` once stabilized to abort.
        let _v = FallbackInCaseThisDidntAbort;
        let _v = CauseDoublePanic;
        panic!();
    }
}

