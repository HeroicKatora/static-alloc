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
    let alloc = memory.get_layout(rc::Rc::<HotPotato>::layout()).unwrap();
    let ptr = alloc.uninit.as_non_null();
    let mut foo = rc::Rc::new(HotPotato(0), alloc.uninit);

    rc::Rc::get_mut(&mut foo).unwrap().0 = 4;
    // Create a second Rc
    let foo2 = rc::Rc::clone(&foo);
    assert!(rc::Rc::get_mut(&mut foo).is_none());

    // Drop the second, now unique again.
    drop(foo2);
    assert!(rc::Rc::get_mut(&mut foo).is_some());

    let (val, weak) = rc::Rc::try_unwrap(foo).ok().unwrap();
    assert_eq!(rc::Weak::strong_count(&weak), 0);
    assert_eq!(rc::Weak::weak_count(&weak), 1);

    let mem = rc::Weak::try_unwrap(weak).ok().unwrap();
    assert_eq!(ptr, mem.as_non_null());

    mem::forget(val);
}
