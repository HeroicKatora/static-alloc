use core::mem::{self, MaybeUninit};
use static_alloc::{FixedVec, Slab, Uninit};

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

    // This should be exactly enough to fulfill the request.
    let slab: Slab<[usize; 16]> = Slab::uninit();
    let vec = slab.fixed_vec::<usize>(16).unwrap();
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_eq!(vec.capacity(), 16);
}

#[test]
fn indexing() {
    let mut memory: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
    let uninit = Uninit::from(&mut memory).cast_slice().unwrap();
    let mut vec = FixedVec::<u8>::new(uninit);

    assert_eq!(&vec[..], []);
    vec.push(0).unwrap();
    assert_eq!(&vec[..], [0]);
    assert_eq!(&vec[1..], []);
    vec[0] = 1;
    assert_eq!(vec.pop(), Some(1));
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

#[test]
fn truncations() {
    use core::cell::Cell;

    #[derive(Debug)]
    struct DropCounted<'a>(&'a Cell<usize>);

    impl Drop for DropCounted<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let drops: Cell<usize> = Cell::new(0);

    let mut memory: MaybeUninit<[usize; 1024]> = MaybeUninit::uninit();
    let uninit = Uninit::from(&mut memory).cast_slice().unwrap();
    let mut vec = FixedVec::new(uninit);

    for _ in 0..16 {
        vec.push(DropCounted(&drops)).unwrap();
    }

    assert_eq!(drops.get(), 0);
    vec.truncate(8);
    assert_eq!(drops.get(), 8);
    vec.truncate(8);
    assert_eq!(drops.get(), 8);
    vec.truncate(16);
    assert_eq!(drops.get(), 8);
    vec.truncate(7);
    assert_eq!(drops.get(), 9);
    vec.truncate(8);
    assert_eq!(drops.get(), 9);
    vec.truncate(1);
    assert_eq!(drops.get(), 15);
    vec.truncate(0);
    assert_eq!(drops.get(), 16);
    vec.truncate(0);
    assert_eq!(drops.get(), 16);
    vec.clear();
    assert_eq!(drops.get(), 16);
}

#[test]
fn hashing() {
    use std::collections::HashMap;
    const KEY: &[usize] = &[0, 1, 2, 3];
    const VAL: &str = "mapped";
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let mut key = memory.fixed_vec(4).unwrap();
    assert_eq!(key.fill(KEY.iter().cloned()).len(), 0);

    let map = Some((key, VAL))
        .into_iter()
        .collect::<HashMap<_, _>>();

    assert_eq!(map.get(KEY).cloned(), Some(VAL));
}
