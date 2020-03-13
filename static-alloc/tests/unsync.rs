use static_alloc::unsync::Bump;

#[test]
fn unsync_bump() {
    let bump = Bump::new(20).unwrap();

    let mut n1 = bump.alloc(10usize).unwrap();
    assert_eq!(bump.remaining_capacity(), 12);

    let mut n2 = bump.alloc(20usize).unwrap();
    assert_eq!(bump.remaining_capacity(), 4);

    let mut n3 = bump.alloc(30i32).unwrap();
    assert_eq!(bump.remaining_capacity(), 0);

    assert!(bump.alloc(10usize).is_err());

    bump.chain(Bump::new(40).unwrap());
    assert!(bump.alloc(10usize).is_ok());

    *n1 += 1;
    *n2 += 2;
    *n3 += 3;

    assert_eq!(*n1, 11);
    assert_eq!(*n2, 22);
    assert_eq!(*n3, 33);
}
