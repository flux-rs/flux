mod common;

tests! {
    sur00 : "../tests/neg/sur00.rs"  => Unsafe,
    test00: "../tests/neg/test00.rs" => Unsafe,
    test01: "../tests/neg/test01.rs" => Unsafe,
    test02: "../tests/neg/test02.rs" => Unsafe,
    test03: "../tests/neg/test03.rs" => Unsafe,
    // Note: only fails if line 329 of liquid-rust-typeck/src/checker.rs is uncommented
    // assert_terminator: "../tests/neg/assert_terminator.rs" => Unsafe,
    fib_loop: "../tests/neg/fib_loop.rs" => Unsafe,
}
