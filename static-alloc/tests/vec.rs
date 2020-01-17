use static_alloc::Bump;

#[global_allocator]
static A: Bump<[u8; 1 << 20]> = Bump::uninit();

#[test]
fn ok_vec() {
    let v = vec![0xdeadbeef_u32; 128];
    println!("{:x?}", v);
    v.into_iter()
        .for_each(|x| assert_eq!(x, 0xdeadbeef_u32));
}
