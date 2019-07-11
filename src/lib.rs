//! General purpose global allocator(s) with static storage.
//!
//! Provides an allocator for extremely resource constrained environments where the only memory
//! guaranteed is your program's image in memory as provided by the loader. Possible use cases are
//! OS-less development, embedded, bootloaders (even stage0/1 maybe, totally untested).
//!
//! ## Usage
//!
//! ```rust
//! use static_alloc::Slab;
//!
//! #[global_allocator]
//! static A: Slab<[u8; 1 << 16]> = Slab::uninit();
//!
//! fn main() {
//!     let v = vec![0xdeadbeef_u32; 128];
//!     println!("{:x?}", v);
//! }
//! ```

// Copyright 2019 Andreas Molzer
#![no_std]

use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::mem::{self, MaybeUninit};
use core::ptr::null_mut;
use core::sync::atomic::{AtomicUsize, Ordering};

/// An allocator whose memory resource has static storage duration.
///
/// The type parameter `T` is used mostly to annotate the required size and alignment of the region
/// and has no futher use. Note that in particular there is no safe way to retrieve or unwrap an
/// inner instance even if the `Slab` was not constructed as a shared global static.
///
/// ## Usage as global allocator
///
/// You can use the stable rust attribute to use an instance of this type as the global allocator.
///
/// ```rust,no_run
/// use static_alloc::Slab;
///
/// #[global_allocator]
/// static A: Slab<[u8; 1 << 16]> = Slab::uninit();
///
/// fn main() { }
/// ```
///
/// Take care, some runtime features of Rust will allocator some memory before or after your own
/// code. In particular, it was found to be be tricky to find out more on the usage of the builtin
/// test framework which seemingly allocates some structures per test.
///
/// ## Usage as a (local) bag of bits
///
/// It is of course entirely possible to use a local instance instead of a single global allocator.
/// For example you could utilize the pointer interface directly to build a `#[no_std]` dynamic
/// data structure in an environment without `extern lib alloc`. This feature was the original
/// motivation behind the crate but no such data structures are provided here so a quick sketch of
/// the idea must do:
///
/// ```
/// use core::alloc;
/// use static_alloc::Slab;
///
/// #[repr(align(4096))]
/// struct PageTable {
///     // some non-trivial type.
/// #   _private: [u8; 4096],
/// }
///
/// impl PageTable {
///     pub unsafe fn new(into: *mut u8) -> &'static mut Self {
///         // ...
/// #       &mut *(into as *mut Self)
///     }
/// }
///
/// // Allocator for pages for page tables. Provides 64 pages. When the
/// // program/kernel is provided as an ELF the bootloader reserves
/// // memory for us as part of the loading process that we can use
/// // purely for page tables. Replaces asm `paging: .BYTE <size>;`
/// static Paging: Slab<[u8; 1 << 18]> = Slab::uninit();
///
/// fn main() {
///     let layout = alloc::Layout::new::<PageTable>();
///     let memory = Paging.alloc(layout).unwrap();
///     let table = unsafe {
///         PageTable::new(memory)
///     };
/// }
/// ```
///
/// A similar structure would of course work to allocate some non-`'static' objects from a
/// temporary `Slab`.
///
/// ## More insights
///
/// WIP: May want to wrap moving values into an allocate region into a safe abstraction with
/// correct lifetimes. This would include slices.
pub struct Slab<T> {
    consumed: AtomicUsize,
    // Outer unsafe cell due to thread safety.
    // Inner MaybeUninit because we padding may destroy initialization invariant
    // on the bytes themselves, and hence drop etc must not assumed inited.
    storage: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Slab<T> {
    /// Make a new allocatable slab of certain byte size and alignment.
    ///
    /// The storage will contain uninitialized bytes.
    pub const fn uninit() -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Make a new allocatable slab of certain byte size and alignment.
    ///
    /// The storage will contain zeroed bytes. This is not *yet* available
    /// as a `const fn` which currently limits its potential usefulness
    /// but there is no good reason not to provide it regardless.
    pub fn zeroed() -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::zeroed()),
        }
    }

    /// Make a new allocatable slab provided with some bytes it can hand out.
    ///
    /// Note that `storage` will never be dropped and there is no way to get it back.
    pub const fn new(storage: T) -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::new(storage)),
        }
    }

    /// Allocate a region of memory.
    ///
    /// This is a safe alternative to [GlobalAlloc::alloc](#impl-GlobalAlloc).
    ///
    /// # Panics
    /// This function will panic if the requested layout has a size of `0`. For the use in a
    /// `GlobalAlloc` this is explicitely forbidden to request and would allow any behaviour but we
    /// instead strictly check it.
    pub fn alloc(&self, layout: Layout) -> Option<*mut u8> {
        let length = mem::size_of::<T>();
        let base_ptr = self.storage.get()
            as *mut T
            as *mut u8;
        
        let alignment = layout.align();
        let requested = layout.size();
        assert!(requested > 0, "Violated allocation requirement: Requested region of size 0");
        
        // Guess zero, this will fail when we try to access it and it isn't.
        let mut consumed = 0;
        loop {
            // Holds due to the stores below.
            let available = length.checked_sub(consumed).unwrap();
            let ptr_to = base_ptr.wrapping_add(consumed);
            let offset = ptr_to.align_offset(alignment);
            
            if requested > available.saturating_sub(offset) {
                return None; // exhausted
            }
            
            // `size` can not be zero, saturation will thus always make this true.
            assert!(offset < available);
            let at_aligned = consumed.checked_add(offset).unwrap();
            let allocated = at_aligned.checked_add(requested).unwrap();
            // allocated 
            //    = consumed + offset + requested  [lines above]
            //   <= consumed + available  [bail out: exhausted]
            //   <= length  [first line of loop]
            // So it's ok to store `allocated` into `consumed`.
            assert!(allocated <= length);
            assert!(at_aligned < length);
            
            // Try to actually allocate. Here we may store `allocated`.
            let observed = self.consumed.compare_and_swap(
                consumed,
                allocated,
                Ordering::SeqCst);
            
            if observed != consumed {
                // Someone else was faster, recalculate again.
                consumed = observed;
                continue;
            }
            
            let aligned = unsafe {
                // SAFETY: 
                // * `0 <= at_aligned < length` in bounds as checked above.
                (base_ptr as *mut u8).add(at_aligned)
            };
            
            return Some(aligned);
        }
    }
}

// SAFETY: at most one thread gets a pointer to each chunk of data.
unsafe impl<T> Sync for Slab<T> { }

unsafe impl<T> GlobalAlloc for Slab<T> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Slab::alloc(self, layout).unwrap_or_else(null_mut)
    }
    
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}
