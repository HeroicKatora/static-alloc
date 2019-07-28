use core::mem::MaybeUninit;
use static_alloc::{rc, Slab};

#[test]
fn create() {
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let rc = memory.rc(0usize).unwrap();
    assert_eq!(rc::Rc::strong_count(&rc), 1);
    assert_eq!(rc::Rc::strong_count(&rc), 0);
}

#[test]
#[should_panic]
fn failed_memory_layout() {
    let mut memory: MaybeUninit<()> = MaybeUninit::uninit();
    rc::Rc::new(0usize, (&mut memory).into());
}
