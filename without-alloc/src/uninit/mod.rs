//! Safe abstractions around pointing at uninitialized memory without references.
//!
//! It is potentially **UB** to have references to uninitialized memory even if such a reference is
//! not 'used' in any particular manner. See [the discussion of the unsafe working group][wg-ref].
//!
//! [wg-ref]: https://github.com/rust-lang/unsafe-code-guidelines/issues/77
mod uninit;
mod ptr_layout;

pub use uninit::{Uninit, UninitView};
pub use ptr_layout::PtrLayout;
