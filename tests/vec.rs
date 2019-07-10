use static_alloc::Slab;

#[global_allocator]
static A: Slab<[u8; 1 << 16]> = unsafe {
    Slab::new([0; 1 << 16])
};

#[test]
fn ok_vec() {
    let v = vec![0xdeadbeef_u32; 128];
    println!("{:x?}", v);
    v.into_iter()
        .for_each(|x| assert_eq!(x, 0xdeadbeef_u32));
}
