mod bump;
#[cfg(feature = "alloc")]
mod chain;

pub use bump::{Bump, MemBump};
#[cfg(feature = "alloc")]
pub use chain::{Chain};
