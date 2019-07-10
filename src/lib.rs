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
//! static A: Slab<[u8; 1 << 16]> = unsafe {
//!     Slab::new([0; 1 << 16])
//! };
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

pub struct Slab<T> {
    consumed: AtomicUsize,
    // Outer unsafe cell due to thread safety.
    // Inner MaybeUninit because we padding may destroy initialization invariant
    // on the bytes themselves, and hence drop etc must not assumed inited.
    storage: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Slab<T> {
    /// Make a new allocatable block provided with some bytes it can hand out.
    ///
    /// Note that `storage` will never be dropped and must not contain any 
    /// uninitialized bytes from padding.
    pub const unsafe fn new(storage: T) -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::new(storage)),
        }
    }
}
    
impl<T> Slab<T> {
    pub fn take(&self, layout: Layout) -> Option<*mut u8> {
        let length = mem::size_of::<T>();
        let base_ptr = self.storage.get()
            as *mut T
            as *mut u8;
        
        let alignment = layout.align();
        let requested = layout.size();
        
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
        self.take(layout).unwrap_or_else(null_mut)
    }
    
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}
