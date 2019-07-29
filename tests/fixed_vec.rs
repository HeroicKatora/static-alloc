use core::mem::{self, MaybeUninit};
use static_alloc::{FixedVec, Uninit};

#[test]
fn create() {
    let vec = FixedVec::<u8>::new(Uninit::empty());
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_eq!(vec.capacity(), 0);

    let mut memory: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
    let uninit = Uninit::from(&mut memory).cast_slice().unwrap();
    let vec = FixedVec::<u8>::new(uninit);
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_eq!(vec.capacity(), 16);
}

#[test]
fn filling() {
    const LEN: usize = 16;

    #[derive(Debug)]
    struct HotPotato(usize);

    impl Drop for HotPotato {
        fn drop(&mut self) {
            panic!("dropped!");
        }
    }

    let mut memory: MaybeUninit<[usize; LEN]> = MaybeUninit::uninit();
    let uninit = Uninit::from(&mut memory).cast_slice().unwrap();
    let mut vec = FixedVec::new(uninit);

    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_eq!(vec.capacity(), 16);

    for i in 0..LEN {
        vec.push(HotPotato(i)).unwrap();
    }

    assert_eq!(vec.len(), 16);
    assert!(!vec.is_empty());
    assert_eq!(vec.capacity(), 16);

    for i in (0..LEN).rev() {
        let val = vec.pop().unwrap();
        assert_eq!(val.0, i);
        mem::forget(val);
    }
}
