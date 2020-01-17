use static_alloc::Bump;

// That's 1 GB. Only rustc/llvm chokes, the `elf` binary itself does not grow. It is up to the
// loader to actually provide that data to our program.
#[global_allocator]
static OMG: Bump<[u8; 1 << 30]> = Bump::uninit();

#[test]
fn ok_vec() {
    let v = vec![0xdeadbeef_u32; 1 << 26];
    v.into_iter()
        .for_each(|x| assert_eq!(x, 0xdeadbeef_u32));
    // If you choose to execute it, you have time to view the program in `top` or w/e.
    std::thread::sleep_ms(10000);
}

