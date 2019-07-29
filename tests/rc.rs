use core::mem;
use static_alloc::{rc, Slab};

#[test]
fn create() {
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let rc = memory.rc(0usize).unwrap();
    assert_eq!(rc::Rc::strong_count(&rc), 1);
    assert_eq!(rc::Rc::weak_count(&rc), 1);
}

#[test]
#[should_panic]
fn failed_memory_layout() {
    let mut memory: mem::MaybeUninit<()> = mem::MaybeUninit::uninit();
    rc::Rc::new(0usize, (&mut memory).into());
}

#[test]
fn reference_juggling() {
    #[derive(Debug)]
    struct HotPotato(usize);

    impl Drop for HotPotato {
        fn drop(&mut self) {
            panic!("dropped!");
        }
    }


    let memory: Slab<[u8; 1024]> = Slab::uninit();
    let mut foo = memory.rc(HotPotato(0)).unwrap();

    rc::Rc::get_mut(&mut foo).unwrap().0 = 4;
    // Create a second Rc
    let foo2 = rc::Rc::clone(&foo);
    assert!(rc::Rc::get_mut(&mut foo).is_none());

    // Drop the second, now unique again.
    drop(foo2);
    assert!(rc::Rc::get_mut(&mut foo).is_some());

    mem::forget(foo);
}
