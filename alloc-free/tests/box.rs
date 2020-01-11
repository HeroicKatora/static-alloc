use alloc_free::alloc::LocalAllocLeakExt;
use alloc_free::boxed::Box;
use static_alloc::Slab;

#[test]
fn recursive() {
    enum List<'a, T> {
        Nil,
        Cons(T, Box<'a, Self>),
    }

    impl<T> List<'_, T> {
        pub fn len(&self) -> usize {
            match self {
                List::Nil => 0,
                List::Cons(_, tail) => 1 + tail.len(),
            }
        }
    }

    let slab: Slab<[usize; 32]> = Slab::uninit();
    let mut list = slab.boxed(List::Nil).unwrap();

    for i in 0usize..8 {
        list = slab.boxed(List::Cons(i, list)).unwrap();
    }

    assert_eq!(list.len(), 8);
}
