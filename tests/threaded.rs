use static_alloc::Slab;
use std::thread;

#[test]
fn each_thread_one() {
    const COUNT: usize = 10;
    // Static but not the global allocator.
    static SLAB: Slab<[u64; COUNT]> = Slab::uninit();

    let threads = (0..COUNT).map(|i| thread::spawn(move || {
        SLAB.leak(i).unwrap();
    })).collect::<Vec<_>>();

    threads
        .into_iter()
        .try_for_each(thread::JoinHandle::join)
        .expect("No thread failed to allocate");

    // But now no more left.
    assert!(SLAB.leak(0).is_err());
}
