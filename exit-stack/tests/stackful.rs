use core::cell::Cell;
use core::pin::Pin;

use exit_stack::ExitStack;
use std::rc::Rc;

#[test]
fn run_with_a_stack() {
    struct DropCheck(Rc<Cell<usize>>);

    impl Drop for DropCheck {
        fn drop(&mut self) {
            let val = self.0.get();
            self.0.set(val + 1);
        }
    }

    let drop_target = Rc::new(Cell::default());

    {
        let exit_stack: ExitStack<[usize; 96]> = ExitStack::new();
        pin_utils::pin_mut!(exit_stack);

        for _ in 0..32 {
            let slot = exit_stack.as_ref().slot().unwrap();
            let pinnable = DropCheck(Rc::clone(&drop_target));
            // A pinned value, but we're using the outer stack space.
            let _: Pin<_> = slot.pin(pinnable);
        }
    }

    assert_eq!(drop_target.get(), 32, "Not dropped as often as expected");
}

#[test]
fn run_with_a_heap_stack() {
    struct DropCheck(Rc<Cell<usize>>);

    impl Drop for DropCheck {
        fn drop(&mut self) {
            let val = self.0.get();
            self.0.set(val + 1);
        }
    }

    let drop_target = Rc::new(Cell::default());

    {
        let exit_stack: Pin<Box<ExitStack<[usize; 2048]>>> = Box::pin(ExitStack::new());

        for _ in 0..32 {
            let slot = exit_stack.as_ref().slot().unwrap();
            let pinnable = DropCheck(Rc::clone(&drop_target));
            // A pinned value, but we're using space of the heap, pinned to the stack. Crazy.
            let _: Pin<_> = slot.pin(pinnable);
        }
    }

    assert_eq!(drop_target.get(), 32, "Not dropped as often as expected");
}
