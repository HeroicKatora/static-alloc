#![no_std]
use core::cell::Cell;
use core::mem::MaybeUninit;
use core::pin::Pin;
use core::ptr::NonNull;

use static_alloc::leaked::LeakBox;
use static_alloc::unsync::Bump;

pub struct ExitStack<Mem> {
    memory: Bump<Mem>,
    top: Cell<Option<ExitHandle>>,
}

type ExitHandle = NonNull<PinSlot<dyn Drop>>;

pub struct ExitStackSlot<'lt, T> {
    /// Where we will commit ourselves to pin the value. If we write a pointer here then it _must_
    /// be dropped before the box's memory is invalidated.
    slotter: &'lt Cell<Option<ExitHandle>>,
    /// The slot which we can fill with a value and meta data.
    value: LeakBox<'lt, MaybeUninit<PinSlot<T>>>,
}

/// One entry in the exit stack linked list.
struct PinSlot<T: ?Sized> {
    link: Option<ExitHandle>,
    value: T,
}

impl<Mem> ExitStack<Mem> {
    pub fn new() -> Self {
        ExitStack {
            memory: Bump::uninit(),
            top: Cell::new(None),
        }
    }

    /// Prepare a slot for pinning a value to the stack.
    pub fn slot<'stack, T: 'static>(self: Pin<&'stack Self>)
        -> Option<ExitStackSlot<'stack, T>>
    {
        let this: &'stack Self = self.get_ref();
        let value = this.memory.bump_box().ok()?;
        Some(ExitStackSlot {
            slotter: &this.top,
            value,
        })
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
    }
}

impl<'lt, T> ExitStackSlot<'lt, T> {
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

    #[allow(dead_code)] // Might pub this later.
    unsafe fn pin_local(self, _: T) -> Pin<&'lt mut T> {
        unimplemented!()
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

