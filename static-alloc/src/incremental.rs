use crate::bump::{Allocation, Bump, Level};

unsafe trait LeveledAllocator {
    fn level(&self) -> Level;
}

pub use SliceBuilder<'a> {
}
