use core::cell::Cell;
use core::pin::Pin;

use exit_stack::ExitStack;
use std::rc::Rc;

#[test]
fn run_with_a_stack() {
    let drop_target = Rc::new(Cell::default());

    {
        let exit_stack: ExitStack<[usize; 96]> = ExitStack::new();
        pin_utils::pin_mut!(exit_stack);

        for _ in 0..32 {
            let slot = exit_stack.as_ref().slot().unwrap();
            let pinnable = DropCheck::new(&drop_target);
            // A pinned value, but we're using the outer stack space.
            let _: Pin<_> = slot.pin(pinnable);
        }
    }

    assert_eq!(drop_target.get(), 32, "Not dropped as often as expected");
}

#[test]
fn run_with_a_heap_stack() {
    let drop_target = Rc::new(Cell::default());

    {
        let exit_stack: Pin<Box<ExitStack<[usize; 2048]>>> = Box::pin(ExitStack::new());

        for _ in 0..32 {
            let slot = exit_stack.as_ref().slot().unwrap();
            let pinnable = DropCheck::new(&drop_target);
            // A pinned value, but we're using space of the heap, pinned to the stack. Crazy.
            let _: Pin<_> = slot.pin(pinnable);
        }
    }

    assert_eq!(drop_target.get(), 32, "Not dropped as often as expected");
}

#[test]
fn set_with_various_sizes() {
    fn set_with_t<T: Default + 'static>() {
        let exit_stack: ExitStack<T> = ExitStack::new();
        pin_utils::pin_mut!(exit_stack);
        let _ = exit_stack.set(T::default());
    }

    #[derive(Default)]
    struct Zst;
    #[derive(Default)]
    struct Large([u64; 32]);

    set_with_t::<Zst>();
    set_with_t::<Large>();
}

#[test]
fn set_drops_correctly() {
    let drop_target = Default::default();

    {
        let exit_stack: ExitStack<DropCheck> = ExitStack::new();
        pin_utils::pin_mut!(exit_stack);
        // Check that this succeeds.
        let _ = exit_stack.as_mut().set(DropCheck::new(&drop_target));
        // Didn't drop any value yet, though we didn't capture it.
        assert_eq!(drop_target.get(), 0);

        // Check that this succeeds, a second time.
        let _ = exit_stack.set(DropCheck::new(&drop_target));
        // The first was dropped as part of this.
        assert_eq!(drop_target.get(), 1);
    }

    // Now the exit_stack was dropped, and the second value with it.
    assert_eq!(drop_target.get(), 2);
}

struct DropCheck(Rc<Cell<usize>>);

impl Drop for DropCheck {
    fn drop(&mut self) {
        let val = self.0.get();
        self.0.set(val + 1);
    }
}

impl DropCheck {
    fn new(cell: &'_ Rc<Cell<usize>>) -> Self {
        DropCheck(Rc::clone(cell))
    }
}
