use core::num::NonZeroU16;

use static_alloc::Slab;

#[test]
fn homogeneous() {
    let slab = Slab::<[u64; 3]>::uninit();

    let new_zero = slab.leak(0_u64).unwrap();
    assert_eq!(*new_zero, 0);

    let next = slab.leak(255_u64).unwrap();
    assert_eq!(*next, 255);
    assert_eq!(*new_zero, 0);

    let last = slab.leak(u64::max_value()).unwrap();
    assert_eq!(*next, 255);
    assert_eq!(*new_zero, 0);
    assert_eq!(*last, u64::max_value());

    assert!(slab.leak(0_u8).is_err());
}

#[test]
fn heterogeneous() {
    // Avoids additional space usage from alignments: all 3 values fit for an aligned `u16`.
    let slab = Slab::<[u16; 3]>::uninit();

    let intu16: &mut u16 = slab.leak(0).unwrap();
    assert_eq!(*intu16, 0);

    let option: &mut Option<u8> = slab.leak(Some(0_u8)).unwrap();
    assert_eq!(*option, Some(0));

    let nonzero: &mut Option<NonZeroU16> = slab.leak(None).unwrap();
    assert_eq!(*nonzero, None);

    assert!(slab.leak(0_u8).is_err());
}

#[test]
fn zst() {
    let slab = Slab::<()>::uninit();

    slab.leak::<()>(())
        .expect("Could 'allocate' zst in no space");
}
