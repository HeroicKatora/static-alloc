use fill::Fill;

#[test]
fn slice() {
    let mut memory = [0u8; 8];
    let tail = memory.iter_mut().fill_and_keep_tail(0..);

    assert_eq!(memory, [0, 1, 2, 3, 4, 5, 6, 7]);
    assert_eq!(tail.start, 8);
}

#[test]
fn slice_and_swap() {
    let mut zero = [0u8; 2];
    let mut ones = [1u8; 4];

    zero.iter_mut().fill(ones.iter_mut());
    assert_eq!(zero, [1, 1]);
    assert_eq!(ones, [0, 0, 1, 1]);
}

#[test]
fn option() {
    let mut slot = None;
    slot.fill(Some(42));
    assert_eq!(slot, Some(42));

    slot.fill(Some(0xFF));
    assert_eq!(slot, Some(42));
}

#[test]
fn result() {
    let mut memory = [0u8; 4];
    let mut free = Ok(memory.iter_mut());

    let unfilled = free.fill_and_keep_tail((0..2).map(Ok));
    assert_eq!(free.as_ref().ok().unwrap().len(), 2);
    assert_eq!(unfilled.len(), 0);

    let unfilled = free.fill_and_keep_tail(vec![Err(0xee), Ok(4)]);
    assert_eq!(free.err(), Some(0xee));
    assert_eq!(unfilled.len(), 1);

    assert_eq!(memory, [0, 1, 0, 0]);
}
