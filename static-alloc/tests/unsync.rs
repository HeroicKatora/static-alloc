use static_alloc::unsync::Chain;

#[test]
fn unsync_bump() {
    let chain = Chain::new(20).unwrap();

    let mut n1 = chain.try_alloc(10usize).unwrap();
    assert_eq!(chain.remaining_capacity(), 12);

    let mut n2 = chain.try_alloc(20usize).unwrap();
    assert_eq!(chain.remaining_capacity(), 4);

    let mut n3 = chain.try_alloc(30i32).unwrap();
    assert_eq!(chain.remaining_capacity(), 0);

    assert!(chain.try_alloc(10usize).is_err());

    chain.chain(Chain::new(40).unwrap());
    assert!(chain.try_alloc(10usize).is_ok());

    *n1 += 1;
    *n2 += 2;
    *n3 += 3;

    assert_eq!(*n1, 11);
    assert_eq!(*n2, 22);
    assert_eq!(*n3, 33);
}
