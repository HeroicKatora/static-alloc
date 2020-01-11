// Copyright 2019 Andreas Molzer
#![no_std]
// #![deny(missing_docs)]

pub mod alloc;
pub mod boxed;
pub mod rc;
pub mod uninit;
pub mod fixed_vec;

pub use boxed::Box;
pub use fixed_vec::FixedVec;
pub use uninit::Uninit;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
