#![feature(try_reserve)]

use static_alloc::Slab;

#[global_allocator]
static A: Slab<[u8; 1 << 16]> = Slab::uninit();

#[test]
fn vec_fail_reserve() {
    let mut v: Vec<u8> = Vec::new();
    assert!(v.try_reserve((1 << 16) + 1).is_err());
}
