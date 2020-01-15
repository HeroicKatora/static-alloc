use core::mem;
use core::convert::TryInto;
use without_alloc::alloc::LocalAllocLeakExt;
use without_alloc::rc;
use static_alloc::Slab;

#[test]
fn create() {
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let rc = memory.rc(0usize).unwrap();
    assert_eq!(rc::Rc::strong_count(&rc), 1);
    assert_eq!(rc::Rc::weak_count(&rc), 1);

    assert_eq!(rc.wrapping_add(1), 1);
    assert_eq!(*rc.as_ref(), 0);
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
    let layout = rc::Rc::<HotPotato>::layout().try_into().unwrap();
    let alloc = LocalAllocLeakExt::alloc_layout(&memory, layout).unwrap();
    let ptr = alloc.uninit.as_non_null();
    let mut foo = rc::Rc::new(HotPotato(0), alloc.uninit);

    rc::Rc::get_mut(&mut foo).unwrap().0 = 4;
    // Create a second Rc
    let foo2 = rc::Rc::clone(&foo);
    assert!(rc::Rc::get_mut(&mut foo).is_none());

    // Drop the second, now unique again.
    drop(foo2);
    assert!(rc::Rc::get_mut(&mut foo).is_some());

    // A weak pointer will also not allow a reference.
    let weak = rc::Rc::downgrade(&foo);
    assert!(rc::Rc::get_mut(&mut foo).is_none());
    drop(weak);

    let (val, weak) = rc::Rc::try_unwrap(foo).ok().unwrap();
    assert_eq!(rc::Weak::strong_count(&weak), 0);
    assert_eq!(rc::Weak::weak_count(&weak), 1);

    let mem = rc::Weak::try_unwrap(weak).ok().unwrap();
    assert_eq!(ptr, mem.as_non_null());

    mem::forget(val);
}

#[test]
fn raw_and_back() {
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let rc = memory.rc(0usize).unwrap();
    assert_eq!(rc::Rc::strong_count(&rc), 1);
    assert_eq!(rc::Rc::weak_count(&rc), 1);

    let raw = rc::Rc::into_raw(rc).ok().unwrap();
    let ptr_to_val = raw.as_non_null();

    let mut rc = unsafe { rc::Rc::from_raw(raw) };
    assert_eq!(rc::Rc::get_mut(&mut rc).unwrap() as *mut _, ptr_to_val.as_ptr());
}

#[test]
fn downgrade_upgrade() {
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let rc = memory.rc(0usize).unwrap();
    assert_eq!(rc::Rc::strong_count(&rc), 1);
    assert_eq!(rc::Rc::weak_count(&rc), 1);

    let weak = rc::Rc::downgrade(&rc);
    let rc2 = weak.upgrade().unwrap();

    assert_eq!(rc::Rc::strong_count(&rc), 2);
    assert_eq!(rc::Rc::weak_count(&rc), 2);
    drop(weak);

    drop(rc);
    let (_, weak) = rc::Rc::try_unwrap(rc2).ok().unwrap();
    assert_eq!(weak.strong_count(), 0);
    assert_eq!(weak.weak_count(), 1);

    assert!(weak.upgrade().is_none());
}

#[test]
fn compares() {
    use std::cmp::PartialEq;
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let zero = memory.rc(0usize).unwrap();
    let one = memory.rc(1usize).unwrap();

    assert_eq!(zero, zero);
    assert_eq!(one, one);
    assert!(!PartialEq::ne(&zero, &zero));
    assert_ne!(zero, one);

    assert!(zero < one);
    assert!(zero <= one);
    assert!(one > zero);
    assert!(one >= zero);
}

#[test]
fn hashing() {
    use std::collections::HashMap;
    const KEY: usize = 0xdeadbeef;
    const VAL: &str = "mapped";
    let memory: Slab<[u8; 1024]> = Slab::uninit();

    let value = memory.rc(KEY).unwrap();
    let map = Some((value, VAL))
        .into_iter()
        .collect::<HashMap<_, _>>();

    assert_eq!(map.get(&KEY).cloned(), Some(VAL));
}
