use static_alloc::unsync::Bump;

#[test]
fn unsync_bump() {
    let mut bump = Bump::new(20).unwrap();

    let n1 = bump.alloc(10usize).unwrap();
    let n2 = bump.alloc(20usize).unwrap();
    let n3 = bump.alloc(10i32).unwrap();

    assert!(bump.alloc(10usize).is_err());

    bump.chain(Bump::new(40).unwrap());
    assert!(bump.alloc(10usize).is_ok());
}