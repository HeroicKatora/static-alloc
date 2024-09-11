//! Tests that require the `alloc` feature.
#![cfg(feature = "alloc")]
use std::fmt::Debug;
use std::rc::Rc;
use std::sync::Arc;

use unsize::{Coercion, CoerceUnsized, CoerciblePtr};


/// Does an arbitrary coercion for `dyn Debug`
fn arbitrary_debug<T: CoerciblePtr<dyn Debug, Output=U>, U>(ptr: T) -> U
    where T::Pointee: Debug + 'static {
    ptr.unsize(Coercion::to_debug())
}

const TEST_VAL: &str = "foo";
fn check_debug<U: AsRef<dyn Debug>>(val: U) {
    assert_eq!(format!("{:?}", val.as_ref()), format!("{:?}", TEST_VAL))
}

#[test]
fn smart_ptrs() {
    check_debug(arbitrary_debug::<Box<String>, Box<dyn Debug>>(Box::new(TEST_VAL.into())));
    check_debug(arbitrary_debug::<Rc<String>, Rc<dyn Debug>>(Rc::new(TEST_VAL.into())));
    check_debug(arbitrary_debug::<Arc<String>, Arc<dyn Debug>>(Arc::new(TEST_VAL.into())));
}