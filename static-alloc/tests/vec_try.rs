#![feature(try_reserve)]

use static_alloc::Bump;

#[global_allocator]
static A: Bump<[u8; 1 << 16]> = Bump::uninit();

#[test]
fn vec_fail_reserve() {
    let mut v: Vec<u8> = Vec::new();
    assert!(v.try_reserve((1 << 16) + 1).is_err());
}
