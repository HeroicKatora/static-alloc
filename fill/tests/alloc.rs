use fill::Fill;

#[test]
fn vec() {
    let mut vec = Vec::with_capacity(10);
    let tail = vec.fill(0..20);
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.capacity(), 10);
    assert_eq!(tail.len(), 10);

    for _ in 0..5 { let _ = vec.pop(); }
    let tail = vec.fill(tail);
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.capacity(), 10);
    assert_eq!(tail.len(), 5);

    vec.truncate(0);
    let tail = vec.fill(tail);
    assert_eq!(vec.len(), 5);
    assert_eq!(vec.capacity(), 10);
    assert_eq!(tail.len(), 0);
}


#[test]
fn vec_deque() {
    use std::collections::VecDeque;
    let mut queue = VecDeque::with_capacity(10);
    let tail = queue.fill(0..20);
    assert_eq!(queue.len(), queue.capacity());
    assert_eq!(tail.len(), 20 - queue.len());

}
