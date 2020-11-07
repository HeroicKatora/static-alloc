use core::{cell::RefCell, mem::MaybeUninit};
use static_alloc::{Bump, leaked::LeakBox};

#[test]
fn leak_box_drops() {
    let bump: Bump<[*const (); 4]> = Bump::uninit();
    let cell = RefCell::new(());
    assert!(cell.try_borrow().is_ok());

    let _ = bump.boxed(cell.borrow()).unwrap();
    assert!(cell.try_borrow().is_ok(), "Immediately dropped it");
    assert!(cell.try_borrow_mut().is_ok(), "Immediately dropped it");

    let boxed = bump.boxed(cell.borrow()).unwrap();
    assert!(cell.try_borrow().is_ok(), "Borrow works, of course");
    assert!(cell.try_borrow_mut().is_err(), "Still borrowed");
    drop(boxed);

    assert!(cell.try_borrow_mut().is_ok(), "No longer borrowed");
}

#[test]
fn leaking() {
    struct PanicOnDrop(usize);
    impl Drop for PanicOnDrop {
        fn drop(&mut self) {
            panic!("Do not drop me.");
        }
    }

    let bump: Bump<[usize; 1]> = Bump::uninit();
    let boxed = bump.boxed(PanicOnDrop(0)).unwrap();
    core::mem::forget(boxed);
    // Panic averted.
}

#[test]
fn init() {
    let bump: Bump<[usize; 1]> = Bump::uninit();
    let boxed = bump.boxed(MaybeUninit::uninit()).unwrap();
    let init = LeakBox::write(boxed, 0usize);
    assert_eq!(*init, 0usize);
}

#[test]
fn trait_impls() {
    let mut memory = MaybeUninit::uninit();
    let mut boxed = LeakBox::write(LeakBox::from(&mut memory), 0usize);

    // AsMut and AsRef
    *boxed.as_mut() = 1;
    assert_eq!(1usize, *boxed.as_ref());
    // Deref and DerefMut
    *boxed = 2;
    assert_eq!(2usize, *boxed);
    // Debug, Display, Pointer
    println!("{:?}", boxed);
    println!("{}", boxed);
    println!("{:p}", boxed);
}
