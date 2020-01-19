use fill::Fill;

#[test]
fn vec() {
    let mut vec = Vec::with_capacity(10);
    let tail = vec.fill(0..20);
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.capacity(), 10);
    assert_eq!(tail.len(), 10);
}
