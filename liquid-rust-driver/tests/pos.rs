mod common;

tests! {
    sur00 : "../tests/pos/sur00.rs"  => Safe,
    test00: "../tests/pos/test00.rs" => Safe,
    test01: "../tests/pos/test01.rs" => Safe,
    test02: "../tests/pos/test02.rs" => Safe,
    test03: "../tests/pos/test03.rs" => Safe,
    generalized_join: "../tests/pos/generalized_join.rs" => Safe,
    heapsort: "../tests/pos/heapsort.rs" => Safe,
    assert_terminator: "../tests/pos/assert_terminator.rs" => Safe,
    fib_loop: "../tests/pos/fib_loop.rs" => Safe,
}
