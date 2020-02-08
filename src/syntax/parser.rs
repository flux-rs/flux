// auto-generated: "lalrpop 0.17.2"
// sha256: 4b2462d6482df8ebdd224b3f20da2c3ef146ad85ebc4afbab637f90631aa784
#![allow(clippy::all)]
#![allow(unused_parens)]
use std::str::FromStr;
use super::span_with_offset;
use crate::syntax::ast::*;
use rustc_span::{symbol::Symbol, hygiene::SyntaxContext, BytePos};
#[allow(unused_extern_crates)]
extern crate lalrpop_util as __lalrpop_util;
#[allow(unused_imports)]
use self::__lalrpop_util::state_machine as __state_machine;

#[cfg_attr(rustfmt, rustfmt_skip)]
mod __parse__FnAnnot {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports, unused_parens)]

    use std::str::FromStr;
    use super::super::span_with_offset;
    use crate::syntax::ast::*;
    use rustc_span::{symbol::Symbol, hygiene::SyntaxContext, BytePos};
    #[allow(unused_extern_crates)]
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(unused_imports)]
    use self::__lalrpop_util::state_machine as __state_machine;
    use super::__intern_token::Token;
    #[allow(dead_code)]
    pub enum __Symbol<'input>
     {
        Variant0(&'input str),
        Variant1(Reft),
        Variant2(::std::vec::Vec<Reft>),
        Variant3(usize),
        Variant4(BinOp),
        Variant5(Box<Pred>),
        Variant6(FnType),
        Variant7(Ident),
        Variant8(Lit),
        Variant9(Name),
        Variant10(BinOpKind),
        Variant11(::std::option::Option<Reft>),
        Variant12(Vec<Reft>),
        Variant13(UnOp),
        Variant14(UnOpKind),
    }
    const __ACTION: &'static [i8] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 2
        0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 0, -53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 0, -55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11,
        // State 7
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 8
        0, 0, 0, -52, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 9
        0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 10
        0, -26, 0, -26, -26, -26, 0, -26, 0, -26, 0, -26, -26, -26, -26, 0, 0, 0, 0, -26, -26, 0, 0,
        // State 11
        0, 0, 0, -54, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 12
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0,
        // State 13
        0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5,
        // State 16
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 17
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11,
        // State 18
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0,
        // State 19
        0, 0, 0, -28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -28, -28, 0, 0,
        // State 20
        0, -30, 0, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, -30, 0, 0,
        // State 21
        0, -16, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 45, 46, 47, 0, 0, 0, 0, -16, -16, 0, 0,
        // State 22
        0, -32, 0, -32, 0, -32, 0, -32, 0, 0, 0, 0, -32, -32, -32, 0, 0, 0, 0, -32, -32, 0, 0,
        // State 23
        0, -34, 0, -34, -34, -34, 0, -34, 0, -34, 0, 0, -34, -34, -34, 0, 0, 0, 0, -34, -34, 0, 0,
        // State 24
        0, -20, 0, -20, -20, -20, 0, -20, 0, -20, 0, 0, -20, -20, -20, 0, 0, 0, 0, -20, -20, 0, 0,
        // State 25
        0, -39, 0, -39, -39, -39, 0, -39, 0, -39, 0, 0, -39, -39, -39, 0, 0, 0, 0, -39, -39, 0, 0,
        // State 26
        0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, -13, 0, 0,
        // State 27
        0, 53, 0, -14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -14, -14, 0, 0,
        // State 28
        0, -17, 0, -17, 0, 56, 0, 57, 0, 0, 0, 0, -17, -17, -17, 0, 0, 0, 0, -17, -17, 0, 0,
        // State 29
        0, -18, 0, -18, 60, -18, 0, -18, 0, 61, 0, 0, -18, -18, -18, 0, 0, 0, 0, -18, -18, 0, 0,
        // State 30
        0, -22, 0, -22, -22, -22, 0, -22, 0, -22, 0, 0, -22, -22, -22, 0, 0, 0, 0, -22, -22, 0, 0,
        // State 31
        0, -21, 0, -21, -21, -21, 0, -21, 0, -21, 0, 0, -21, -21, -21, 0, 0, 0, 0, -21, -21, 0, 0,
        // State 32
        0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 33
        0, 0, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -56, -56, 0, 0, 0, -56, -56,
        // State 34
        0, 0, -57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57, -57, 0, 0, 0, -57, -57,
        // State 35
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 36
        0, 0, -58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -58, -58, 0, 0, 0, -58, -58,
        // State 37
        0, -37, 0, -37, -37, -37, 0, -37, 0, -37, 0, 0, -37, -37, -37, 0, 0, 0, 0, -37, -37, 0, 0,
        // State 38
        0, -36, 0, -36, -36, -36, 0, -36, 0, -36, 0, 0, -36, -36, -36, 0, 0, 0, 0, -36, -36, 0, 0,
        // State 39
        0, -35, 0, -35, -35, -35, 0, -35, 0, -35, 0, 0, -35, -35, -35, 0, 0, 0, 0, -35, -35, 0, 0,
        // State 40
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25, 0, 0, 0, 0, 0, 0, 0,
        // State 41
        0, 0, 0, -49, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0,
        // State 42
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 43
        -10, 0, -10, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -10, -10, 0, 0, 0, -10, -10,
        // State 44
        -42, 0, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42, -42, 0, 0, 0, -42, -42,
        // State 45
        -43, 0, -43, 0, -43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -43, -43, 0, 0, 0, -43, -43,
        // State 46
        -44, 0, -44, 0, -44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -44, -44, 0, 0, 0, -44, -44,
        // State 47
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 48
        -8, 0, -8, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0, -8, -8,
        // State 49
        -40, 0, -40, 0, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -40, 0, 0, 0, -40, -40,
        // State 50
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 51
        -9, 0, -9, 0, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -9, -9, 0, 0, 0, -9, -9,
        // State 52
        -41, 0, -41, 0, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -41, -41, 0, 0, 0, -41, -41,
        // State 53
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 54
        -11, 0, -11, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -11, -11, 0, 0, 0, -11, -11,
        // State 55
        -45, 0, -45, 0, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, -45, 0, 0, 0, -45, -45,
        // State 56
        -46, 0, -46, 0, -46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -46, -46, 0, 0, 0, -46, -46,
        // State 57
        35, 0, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 40, 11,
        // State 58
        -12, 0, -12, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, -12, 0, 0, 0, -12, -12,
        // State 59
        -47, 0, -47, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, -47, 0, 0, 0, -47, -47,
        // State 60
        -48, 0, -48, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48, -48, 0, 0, 0, -48, -48,
        // State 61
        0, -19, 0, -19, -19, -19, 0, -19, 0, -19, 0, 0, -19, -19, -19, 0, 0, 0, 0, -19, -19, 0, 0,
        // State 62
        0, 0, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 63
        0, -15, 0, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, -15, 0, 0,
        // State 64
        0, 0, 0, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, -27, 0, 0,
        // State 65
        0, -29, 0, -29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -29, -29, 0, 0,
        // State 66
        0, -31, 0, -31, 0, -31, 0, -31, 0, 0, 0, 0, -31, -31, -31, 0, 0, 0, 0, -31, -31, 0, 0,
        // State 67
        0, -33, 0, -33, -33, -33, 0, -33, 0, -33, 0, 0, -33, -33, -33, 0, 0, 0, 0, -33, -33, 0, 0,
        // State 68
        0, -23, 0, -23, -23, -23, 0, -23, 0, -23, 0, 0, -23, -23, -23, 0, 0, 0, 0, -23, -23, 0, 0,
    ];
    const __EOF_ACTION: &'static [i8] = &[
        // State 0
        0,
        // State 1
        -59,
        // State 2
        0,
        // State 3
        0,
        // State 4
        0,
        // State 5
        -24,
        // State 6
        0,
        // State 7
        0,
        // State 8
        0,
        // State 9
        0,
        // State 10
        0,
        // State 11
        0,
        // State 12
        0,
        // State 13
        0,
        // State 14
        0,
        // State 15
        0,
        // State 16
        0,
        // State 17
        0,
        // State 18
        0,
        // State 19
        0,
        // State 20
        0,
        // State 21
        0,
        // State 22
        0,
        // State 23
        0,
        // State 24
        0,
        // State 25
        0,
        // State 26
        0,
        // State 27
        0,
        // State 28
        0,
        // State 29
        0,
        // State 30
        0,
        // State 31
        0,
        // State 32
        0,
        // State 33
        0,
        // State 34
        0,
        // State 35
        0,
        // State 36
        0,
        // State 37
        0,
        // State 38
        0,
        // State 39
        0,
        // State 40
        0,
        // State 41
        0,
        // State 42
        0,
        // State 43
        0,
        // State 44
        0,
        // State 45
        0,
        // State 46
        0,
        // State 47
        0,
        // State 48
        0,
        // State 49
        0,
        // State 50
        0,
        // State 51
        0,
        // State 52
        0,
        // State 53
        0,
        // State 54
        0,
        // State 55
        0,
        // State 56
        0,
        // State 57
        0,
        // State 58
        0,
        // State 59
        0,
        // State 60
        0,
        // State 61
        0,
        // State 62
        0,
        // State 63
        0,
        // State 64
        0,
        // State 65
        0,
        // State 66
        0,
        // State 67
        0,
        // State 68
        0,
    ];
    const __GOTO: &'static [i8] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 2
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 10, 0, 0, 0, 0,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0,
        // State 7
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 8
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 9
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 10
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 12
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 13
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 16
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 22, 23, 24, 25, 0, 0, 26, 27, 28, 29, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 17
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0,
        // State 18
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 19
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 20
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 21
        0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 22
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 23
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 24
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 25
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 26
        0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 27
        0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 28
        0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 29
        0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 0,
        // State 30
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 32
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 0, 26, 0, 0, 0, 0, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 33
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 20, 21, 22, 23, 24, 25, 0, 0, 26, 27, 28, 29, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 36
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 37
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 38
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 39
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 40
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 41
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 42
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 23, 24, 25, 0, 0, 26, 0, 0, 29, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 43
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 44
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 45
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 46
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 47
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 21, 22, 23, 24, 25, 0, 0, 26, 0, 28, 29, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 48
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 49
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 50
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 22, 23, 24, 25, 0, 0, 26, 0, 0, 29, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 51
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 52
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 53
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 24, 25, 0, 0, 26, 0, 0, 0, 30, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 54
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 55
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 56
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 57
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 25, 0, 0, 26, 0, 0, 0, 0, 31, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0,
        // State 58
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 59
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 60
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 61
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 62
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 63
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 64
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 65
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 66
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 67
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 68
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    fn __expected_tokens(__state: usize) -> Vec<::std::string::String> {
        const __TERMINAL: &'static [&'static str] = &[
            r###""!""###,
            r###""&&""###,
            r###""(""###,
            r###"")""###,
            r###""*""###,
            r###""+""###,
            r###"",""###,
            r###""-""###,
            r###""->""###,
            r###""/""###,
            r###""/**@""###,
            r###"":""###,
            r###""<""###,
            r###"">""###,
            r###"">=""###,
            r###""@*/""###,
            r###""false""###,
            r###""true""###,
            r###""{""###,
            r###""||""###,
            r###""}""###,
            r###"r#"[0-9]+"#"###,
            r###"r#"[a-zA-Z][a-zA-Z0-9_]*"#"###,
        ];
        __ACTION[(__state * 23)..].iter().zip(__TERMINAL).filter_map(|(&state, terminal)| {
            if state == 0 {
                None
            } else {
                Some(terminal.to_string())
            }
        }).collect()
    }
    pub struct __StateMachine<'input, F>
    where F: Fn() -> ExprId, F: Copy
    {
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __phantom: ::std::marker::PhantomData<(&'input (), F)>,
    }
    impl<'input, F> __state_machine::ParserDefinition for __StateMachine<'input, F>
    where F: Fn() -> ExprId, F: Copy
    {
        type Location = usize;
        type Error = &'static str;
        type Token = Token<'input>;
        type TokenIndex = usize;
        type Symbol = __Symbol<'input>;
        type Success = FnType;
        type StateIndex = i8;
        type Action = i8;
        type ReduceIndex = i8;
        type NonterminalIndex = usize;

        #[inline]
        fn start_location(&self) -> Self::Location {
              Default::default()
        }

        #[inline]
        fn start_state(&self) -> Self::StateIndex {
              0
        }

        #[inline]
        fn token_to_index(&self, token: &Self::Token) -> Option<usize> {
            __token_to_integer(token, ::std::marker::PhantomData::<(&(), F)>)
        }

        #[inline]
        fn action(&self, state: i8, integer: usize) -> i8 {
            __ACTION[(state as usize) * 23 + integer]
        }

        #[inline]
        fn error_action(&self, state: i8) -> i8 {
            __ACTION[(state as usize) * 23 + (23 - 1)]
        }

        #[inline]
        fn eof_action(&self, state: i8) -> i8 {
            __EOF_ACTION[state as usize]
        }

        #[inline]
        fn goto(&self, state: i8, nt: usize) -> i8 {
            __GOTO[(state as usize) * 39 + nt] - 1
        }

        fn token_to_symbol(&self, token_index: usize, token: Self::Token) -> Self::Symbol {
            __token_to_symbol(token_index, token, ::std::marker::PhantomData::<(&(), F)>)
        }

        fn expected_tokens(&self, state: i8) -> Vec<String> {
            __expected_tokens(state as usize)
        }

        #[inline]
        fn uses_error_recovery(&self) -> bool {
            false
        }

        #[inline]
        fn error_recovery_symbol(
            &self,
            recovery: __state_machine::ErrorRecovery<Self>,
        ) -> Self::Symbol {
            panic!("error recovery not enabled for this grammar")
        }

        fn reduce(
            &mut self,
            action: i8,
            start_location: Option<&Self::Location>,
            states: &mut Vec<i8>,
            symbols: &mut Vec<__state_machine::SymbolTriple<Self>>,
        ) -> Option<__state_machine::ParseResult<Self>> {
            __reduce(
                self.offset,
                self.ctxt,
                self.next_expr_id,
                self.input,
                action,
                start_location,
                states,
                symbols,
                ::std::marker::PhantomData::<(&(), F)>,
            )
        }

        fn simulate_reduce(&self, action: i8) -> __state_machine::SimulatedReduce<Self> {
            __simulate_reduce(action, ::std::marker::PhantomData::<(&(), F)>)
        }
    }
    fn __token_to_integer<
        'input,
        F,
    >(
        __token: &Token<'input>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> Option<usize>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match *__token {
            Token(2, _) if true => Some(0),
            Token(3, _) if true => Some(1),
            Token(4, _) if true => Some(2),
            Token(5, _) if true => Some(3),
            Token(6, _) if true => Some(4),
            Token(7, _) if true => Some(5),
            Token(8, _) if true => Some(6),
            Token(9, _) if true => Some(7),
            Token(10, _) if true => Some(8),
            Token(11, _) if true => Some(9),
            Token(12, _) if true => Some(10),
            Token(13, _) if true => Some(11),
            Token(14, _) if true => Some(12),
            Token(15, _) if true => Some(13),
            Token(16, _) if true => Some(14),
            Token(17, _) if true => Some(15),
            Token(18, _) if true => Some(16),
            Token(19, _) if true => Some(17),
            Token(20, _) if true => Some(18),
            Token(21, _) if true => Some(19),
            Token(22, _) if true => Some(20),
            Token(0, _) if true => Some(21),
            Token(1, _) if true => Some(22),
            _ => None,
        }
    }
    fn __token_to_symbol<
        'input,
        F,
    >(
        __token_index: usize,
        __token: Token<'input>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> __Symbol<'input>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match __token_index {
            0 => match __token {
                Token(2, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            1 => match __token {
                Token(3, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            2 => match __token {
                Token(4, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            3 => match __token {
                Token(5, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            4 => match __token {
                Token(6, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            5 => match __token {
                Token(7, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            6 => match __token {
                Token(8, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            7 => match __token {
                Token(9, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            8 => match __token {
                Token(10, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            9 => match __token {
                Token(11, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            10 => match __token {
                Token(12, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            11 => match __token {
                Token(13, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            12 => match __token {
                Token(14, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            13 => match __token {
                Token(15, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            14 => match __token {
                Token(16, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            15 => match __token {
                Token(17, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            16 => match __token {
                Token(18, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            17 => match __token {
                Token(19, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            18 => match __token {
                Token(20, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            19 => match __token {
                Token(21, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            20 => match __token {
                Token(22, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            21 => match __token {
                Token(0, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            22 => match __token {
                Token(1, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
    fn __simulate_reduce<
        'input,
        F,
    >(
        __reduce_index: i8,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> __state_machine::SimulatedReduce<__StateMachine<'input, F>>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match __reduce_index {
            0 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 0,
                }
            }
            1 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 1,
                }
            }
            2 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 1,
                }
            }
            3 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 2,
                }
            }
            4 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 2,
                }
            }
            5 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 3,
                }
            }
            6 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 4,
                }
            }
            7 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 5,
                }
            }
            8 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 6,
                }
            }
            9 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 7,
                }
            }
            10 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 8,
                }
            }
            11 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 9,
                }
            }
            12 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 10,
                }
            }
            13 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 11,
                }
            }
            14 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 12,
                }
            }
            15 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 12,
                }
            }
            16 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 13,
                }
            }
            17 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 14,
                }
            }
            18 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 15,
                }
            }
            19 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 15,
                }
            }
            20 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 16,
                }
            }
            21 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 16,
                }
            }
            22 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 16,
                }
            }
            23 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 17,
                }
            }
            24 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 5,
                    nonterminal_produced: 18,
                }
            }
            25 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 19,
                }
            }
            26 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 20,
                }
            }
            27 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 20,
                }
            }
            28 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 21,
                }
            }
            29 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 21,
                }
            }
            30 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 22,
                }
            }
            31 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 22,
                }
            }
            32 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 23,
                }
            }
            33 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 23,
                }
            }
            34 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            35 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            36 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            37 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 25,
                }
            }
            38 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 26,
                }
            }
            39 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 27,
                }
            }
            40 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 28,
                }
            }
            41 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            42 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            43 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            44 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 30,
                }
            }
            45 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 30,
                }
            }
            46 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 31,
                }
            }
            47 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 31,
                }
            }
            48 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 5,
                    nonterminal_produced: 32,
                }
            }
            49 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 33,
                }
            }
            50 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 33,
                }
            }
            51 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 34,
                }
            }
            52 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 34,
                }
            }
            53 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 34,
                }
            }
            54 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 34,
                }
            }
            55 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 35,
                }
            }
            56 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 36,
                }
            }
            57 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 36,
                }
            }
            58 => __state_machine::SimulatedReduce::Accept,
            59 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 38,
                }
            }
            _ => panic!("invalid reduction index {}", __reduce_index)
        }
    }
    pub struct FnAnnotParser {
        builder: super::__intern_token::__MatcherBuilder,
        _priv: (),
    }

    impl FnAnnotParser {
        pub fn new() -> FnAnnotParser {
            let __builder = super::__intern_token::__MatcherBuilder::new();
            FnAnnotParser {
                builder: __builder,
                _priv: (),
            }
        }

        #[allow(dead_code)]
        pub fn parse<
            'input,
            F,
        >(
            &self,
            offset: BytePos,
            ctxt: SyntaxContext,
            next_expr_id: F,
            input: &'input str,
        ) -> Result<FnType, __lalrpop_util::ParseError<usize, Token<'input>, &'static str>>
        where
            F: Fn() -> ExprId,
            F: Copy,
        {
            let mut __tokens = self.builder.matcher(input);
            let __r = __state_machine::Parser::drive(
                __StateMachine {
                    offset,
                    ctxt,
                    next_expr_id,
                    input,
                    __phantom: ::std::marker::PhantomData::<(&(), F)>,
                },
                __tokens,
            );
            __r
        }
    }
    pub(crate) fn __reduce<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> Option<Result<FnType,__lalrpop_util::ParseError<usize, Token<'input>, &'static str>>>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        let (__pop_states, __nonterminal) = match __action {
            0 => {
                __reduce0(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            1 => {
                __reduce1(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            2 => {
                __reduce2(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            3 => {
                __reduce3(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            4 => {
                __reduce4(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            5 => {
                __reduce5(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            6 => {
                __reduce6(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            7 => {
                __reduce7(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            8 => {
                __reduce8(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            9 => {
                __reduce9(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            10 => {
                __reduce10(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            11 => {
                __reduce11(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            12 => {
                __reduce12(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            13 => {
                __reduce13(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            14 => {
                __reduce14(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            15 => {
                __reduce15(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            16 => {
                __reduce16(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            17 => {
                __reduce17(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            18 => {
                __reduce18(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            19 => {
                __reduce19(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            20 => {
                __reduce20(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            21 => {
                __reduce21(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            22 => {
                __reduce22(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            23 => {
                __reduce23(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            24 => {
                __reduce24(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            25 => {
                __reduce25(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            26 => {
                __reduce26(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            27 => {
                __reduce27(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            28 => {
                __reduce28(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            29 => {
                __reduce29(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            30 => {
                __reduce30(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            31 => {
                __reduce31(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            32 => {
                __reduce32(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            33 => {
                __reduce33(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            34 => {
                __reduce34(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            35 => {
                __reduce35(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            36 => {
                __reduce36(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            37 => {
                __reduce37(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            38 => {
                __reduce38(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            39 => {
                __reduce39(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            40 => {
                __reduce40(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            41 => {
                __reduce41(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            42 => {
                __reduce42(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            43 => {
                __reduce43(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            44 => {
                __reduce44(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            45 => {
                __reduce45(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            46 => {
                __reduce46(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            47 => {
                __reduce47(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            48 => {
                __reduce48(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            49 => {
                __reduce49(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            50 => {
                __reduce50(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            51 => {
                __reduce51(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            52 => {
                __reduce52(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            53 => {
                __reduce53(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            54 => {
                __reduce54(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            55 => {
                __reduce55(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            56 => {
                __reduce56(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            57 => {
                __reduce57(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            58 => {
                // __FnAnnot = FnAnnot => ActionFn(0);
                let __sym0 = __pop_Variant6(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action0::<F>(offset, ctxt, next_expr_id, input, __sym0);
                return Some(Ok(__nt));
            }
            59 => {
                __reduce59(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __states_len = __states.len();
        __states.truncate(__states_len - __pop_states);
        let __state = *__states.last().unwrap() as usize;
        let __next_state = __GOTO[__state * 39 + __nonterminal] - 1;
        __states.push(__next_state);
        None
    }
    fn __pop_Variant4<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, BinOp, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant4(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant10<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, BinOpKind, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant10(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant5<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Box<Pred>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant5(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant6<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, FnType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant6(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant7<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Ident, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant7(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant8<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Lit, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant8(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant9<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Name, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant9(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant1<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Reft, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant1(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant13<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, UnOp, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant13(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant14<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, UnOpKind, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant14(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant12<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Vec<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant12(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant3<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, usize, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant3(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant11<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::option::Option<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant11(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant2<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant2(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant0<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant0(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    pub(crate) fn __reduce0<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",") = Reft, "," => ActionFn(50);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action50::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (2, 0)
    }
    pub(crate) fn __reduce1<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")* =  => ActionFn(48);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action48::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (0, 1)
    }
    pub(crate) fn __reduce2<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")* = (<Reft> ",")+ => ActionFn(49);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action49::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 1)
    }
    pub(crate) fn __reduce3<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")+ = Reft, "," => ActionFn(57);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action57::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (2, 2)
    }
    pub(crate) fn __reduce4<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")+ = (<Reft> ",")+, Reft, "," => ActionFn(58);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action58::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (3, 2)
    }
    pub(crate) fn __reduce5<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // @L =  => ActionFn(45);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action45::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 3)
    }
    pub(crate) fn __reduce6<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // @R =  => ActionFn(44);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action44::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 4)
    }
    pub(crate) fn __reduce7<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup1> = OpGroup1 => ActionFn(80);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action80::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 5)
    }
    pub(crate) fn __reduce8<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup2> = OpGroup2 => ActionFn(81);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action81::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 6)
    }
    pub(crate) fn __reduce9<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup3> = OpGroup3 => ActionFn(82);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action82::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 7)
    }
    pub(crate) fn __reduce10<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup4> = OpGroup4 => ActionFn(83);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action83::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 8)
    }
    pub(crate) fn __reduce11<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup5> = OpGroup5 => ActionFn(84);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action84::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 9)
    }
    pub(crate) fn __reduce12<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel1 = LeftAssoc<OpGroup1, ExprLevel2> => ActionFn(7);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action7::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 10)
    }
    pub(crate) fn __reduce13<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel2 = LeftAssoc<OpGroup2, ExprLevel3> => ActionFn(8);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action8::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 11)
    }
    pub(crate) fn __reduce14<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel3 = ExprLevel4, BinOp<OpGroup3>, ExprLevel4 => ActionFn(85);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action85::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 12)
    }
    pub(crate) fn __reduce15<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel3 = ExprLevel4 => ActionFn(10);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action10::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 12)
    }
    pub(crate) fn __reduce16<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel4 = LeftAssoc<OpGroup4, ExprLevel5> => ActionFn(11);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action11::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 13)
    }
    pub(crate) fn __reduce17<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel5 = LeftAssoc<OpGroup5, ExprLevel6> => ActionFn(12);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action12::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 14)
    }
    pub(crate) fn __reduce18<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel6 = UnOp, ExprLevel7 => ActionFn(86);
        let __sym1 = __pop_Variant5(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action86::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 15)
    }
    pub(crate) fn __reduce19<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel6 = ExprLevel7 => ActionFn(14);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action14::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 15)
    }
    pub(crate) fn __reduce20<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = Name => ActionFn(87);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action87::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 16)
    }
    pub(crate) fn __reduce21<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = Lit => ActionFn(88);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action88::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 16)
    }
    pub(crate) fn __reduce22<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = "(", ExprLevel1, ")" => ActionFn(17);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant5(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action17::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 16)
    }
    pub(crate) fn __reduce23<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // FnAnnot = "/**@", FnType, "@*/" => ActionFn(2);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action2::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 17)
    }
    pub(crate) fn __reduce24<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // FnType = "(", ReftList, ")", "->", Reft => ActionFn(3);
        let __sym4 = __pop_Variant1(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym4.2.clone();
        let __nt = super::__action3::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2, __sym3, __sym4);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (5, 18)
    }
    pub(crate) fn __reduce25<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Ident = r#"[a-zA-Z][a-zA-Z0-9_]*"# => ActionFn(89);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action89::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (1, 19)
    }
    pub(crate) fn __reduce26<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup1, ExprLevel2> = LeftAssoc<OpGroup1, ExprLevel2>, BinOp<OpGroup1>, ExprLevel2 => ActionFn(90);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action90::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 20)
    }
    pub(crate) fn __reduce27<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup1, ExprLevel2> = ExprLevel2 => ActionFn(43);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action43::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 20)
    }
    pub(crate) fn __reduce28<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup2, ExprLevel3> = LeftAssoc<OpGroup2, ExprLevel3>, BinOp<OpGroup2>, ExprLevel3 => ActionFn(91);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action91::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 21)
    }
    pub(crate) fn __reduce29<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup2, ExprLevel3> = ExprLevel3 => ActionFn(41);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action41::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 21)
    }
    pub(crate) fn __reduce30<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup4, ExprLevel5> = LeftAssoc<OpGroup4, ExprLevel5>, BinOp<OpGroup4>, ExprLevel5 => ActionFn(92);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action92::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 22)
    }
    pub(crate) fn __reduce31<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup4, ExprLevel5> = ExprLevel5 => ActionFn(38);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action38::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 22)
    }
    pub(crate) fn __reduce32<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup5, ExprLevel6> = LeftAssoc<OpGroup5, ExprLevel6>, BinOp<OpGroup5>, ExprLevel6 => ActionFn(93);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action93::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 23)
    }
    pub(crate) fn __reduce33<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup5, ExprLevel6> = ExprLevel6 => ActionFn(36);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action36::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 23)
    }
    pub(crate) fn __reduce34<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = r#"[0-9]+"# => ActionFn(94);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action94::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce35<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = "true" => ActionFn(95);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action95::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce36<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = "false" => ActionFn(96);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action96::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce37<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LocalAnnot = "/**@", Reft, "@*/" => ActionFn(4);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action4::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce38<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Name = Ident => ActionFn(32);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action32::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (1, 26)
    }
    pub(crate) fn __reduce39<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup1 = "||" => ActionFn(18);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action18::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 27)
    }
    pub(crate) fn __reduce40<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup2 = "&&" => ActionFn(19);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action19::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce41<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = "<" => ActionFn(20);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action20::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce42<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = ">" => ActionFn(21);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action21::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce43<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = ">=" => ActionFn(22);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action22::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce44<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup4 = "+" => ActionFn(23);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action23::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce45<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup4 = "-" => ActionFn(24);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action24::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce46<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup5 = "*" => ActionFn(25);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action25::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce47<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup5 = "/" => ActionFn(26);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action26::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce48<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft = Ident, ":", "{", ExprLevel1, "}" => ActionFn(97);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant5(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym4.2.clone();
        let __nt = super::__action97::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2, __sym3, __sym4);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (5, 32)
    }
    pub(crate) fn __reduce49<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft? = Reft => ActionFn(46);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action46::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (1, 33)
    }
    pub(crate) fn __reduce50<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft? =  => ActionFn(47);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action47::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (0, 33)
    }
    pub(crate) fn __reduce51<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = Reft => ActionFn(99);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action99::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce52<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList =  => ActionFn(100);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action100::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (0, 34)
    }
    pub(crate) fn __reduce53<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = (<Reft> ",")+, Reft => ActionFn(101);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action101::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (2, 34)
    }
    pub(crate) fn __reduce54<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = (<Reft> ",")+ => ActionFn(102);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action102::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce55<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOp = UnOpKind => ActionFn(98);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action98::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (1, 35)
    }
    pub(crate) fn __reduce56<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOpKind = "!" => ActionFn(27);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action27::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 36)
    }
    pub(crate) fn __reduce57<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOpKind = "*" => ActionFn(28);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action28::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 36)
    }
    pub(crate) fn __reduce59<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // __LocalAnnot = LocalAnnot => ActionFn(1);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action1::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (1, 38)
    }
}
pub use self::__parse__FnAnnot::FnAnnotParser;

#[cfg_attr(rustfmt, rustfmt_skip)]
mod __parse__LocalAnnot {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports, unused_parens)]

    use std::str::FromStr;
    use super::super::span_with_offset;
    use crate::syntax::ast::*;
    use rustc_span::{symbol::Symbol, hygiene::SyntaxContext, BytePos};
    #[allow(unused_extern_crates)]
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(unused_imports)]
    use self::__lalrpop_util::state_machine as __state_machine;
    use super::__intern_token::Token;
    #[allow(dead_code)]
    pub enum __Symbol<'input>
     {
        Variant0(&'input str),
        Variant1(Reft),
        Variant2(::std::vec::Vec<Reft>),
        Variant3(usize),
        Variant4(BinOp),
        Variant5(Box<Pred>),
        Variant6(FnType),
        Variant7(Ident),
        Variant8(Lit),
        Variant9(Name),
        Variant10(BinOpKind),
        Variant11(::std::option::Option<Reft>),
        Variant12(Vec<Reft>),
        Variant13(UnOp),
        Variant14(UnOpKind),
    }
    const __ACTION: &'static [i8] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 2
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
        // State 5
        0, -26, 0, -26, -26, -26, 0, -26, 0, -26, 0, -26, -26, -26, -26, 0, 0, 0, 0, -26, -26, 0, 0,
        // State 6
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0,
        // State 7
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 8
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 9
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0,
        // State 10
        0, 0, 0, -28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -28, -28, 0, 0,
        // State 11
        0, -30, 0, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, -30, 0, 0,
        // State 12
        0, -16, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 35, 36, 37, 0, 0, 0, 0, -16, -16, 0, 0,
        // State 13
        0, -32, 0, -32, 0, -32, 0, -32, 0, 0, 0, 0, -32, -32, -32, 0, 0, 0, 0, -32, -32, 0, 0,
        // State 14
        0, -34, 0, -34, -34, -34, 0, -34, 0, -34, 0, 0, -34, -34, -34, 0, 0, 0, 0, -34, -34, 0, 0,
        // State 15
        0, -20, 0, -20, -20, -20, 0, -20, 0, -20, 0, 0, -20, -20, -20, 0, 0, 0, 0, -20, -20, 0, 0,
        // State 16
        0, -39, 0, -39, -39, -39, 0, -39, 0, -39, 0, 0, -39, -39, -39, 0, 0, 0, 0, -39, -39, 0, 0,
        // State 17
        0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, -13, 0, 0,
        // State 18
        0, 43, 0, -14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -14, -14, 0, 0,
        // State 19
        0, -17, 0, -17, 0, 46, 0, 47, 0, 0, 0, 0, -17, -17, -17, 0, 0, 0, 0, -17, -17, 0, 0,
        // State 20
        0, -18, 0, -18, 50, -18, 0, -18, 0, 51, 0, 0, -18, -18, -18, 0, 0, 0, 0, -18, -18, 0, 0,
        // State 21
        0, -22, 0, -22, -22, -22, 0, -22, 0, -22, 0, 0, -22, -22, -22, 0, 0, 0, 0, -22, -22, 0, 0,
        // State 22
        0, -21, 0, -21, -21, -21, 0, -21, 0, -21, 0, 0, -21, -21, -21, 0, 0, 0, 0, -21, -21, 0, 0,
        // State 23
        0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 24
        0, 0, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -56, -56, 0, 0, 0, -56, -56,
        // State 25
        0, 0, -57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57, -57, 0, 0, 0, -57, -57,
        // State 26
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 27
        0, 0, -58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -58, -58, 0, 0, 0, -58, -58,
        // State 28
        0, -37, 0, -37, -37, -37, 0, -37, 0, -37, 0, 0, -37, -37, -37, 0, 0, 0, 0, -37, -37, 0, 0,
        // State 29
        0, -36, 0, -36, -36, -36, 0, -36, 0, -36, 0, 0, -36, -36, -36, 0, 0, 0, 0, -36, -36, 0, 0,
        // State 30
        0, -35, 0, -35, -35, -35, 0, -35, 0, -35, 0, 0, -35, -35, -35, 0, 0, 0, 0, -35, -35, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0,
        // State 32
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 33
        -10, 0, -10, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -10, -10, 0, 0, 0, -10, -10,
        // State 34
        -42, 0, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42, -42, 0, 0, 0, -42, -42,
        // State 35
        -43, 0, -43, 0, -43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -43, -43, 0, 0, 0, -43, -43,
        // State 36
        -44, 0, -44, 0, -44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -44, -44, 0, 0, 0, -44, -44,
        // State 37
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 38
        -8, 0, -8, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0, -8, -8,
        // State 39
        -40, 0, -40, 0, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -40, 0, 0, 0, -40, -40,
        // State 40
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 41
        -9, 0, -9, 0, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -9, -9, 0, 0, 0, -9, -9,
        // State 42
        -41, 0, -41, 0, -41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -41, -41, 0, 0, 0, -41, -41,
        // State 43
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 44
        -11, 0, -11, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -11, -11, 0, 0, 0, -11, -11,
        // State 45
        -45, 0, -45, 0, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, -45, 0, 0, 0, -45, -45,
        // State 46
        -46, 0, -46, 0, -46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -46, -46, 0, 0, 0, -46, -46,
        // State 47
        26, 0, 27, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 0, 31, 6,
        // State 48
        -12, 0, -12, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, -12, 0, 0, 0, -12, -12,
        // State 49
        -47, 0, -47, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, -47, 0, 0, 0, -47, -47,
        // State 50
        -48, 0, -48, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48, -48, 0, 0, 0, -48, -48,
        // State 51
        0, -19, 0, -19, -19, -19, 0, -19, 0, -19, 0, 0, -19, -19, -19, 0, 0, 0, 0, -19, -19, 0, 0,
        // State 52
        0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 53
        0, -15, 0, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, -15, 0, 0,
        // State 54
        0, 0, 0, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, -27, 0, 0,
        // State 55
        0, -29, 0, -29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -29, -29, 0, 0,
        // State 56
        0, -31, 0, -31, 0, -31, 0, -31, 0, 0, 0, 0, -31, -31, -31, 0, 0, 0, 0, -31, -31, 0, 0,
        // State 57
        0, -33, 0, -33, -33, -33, 0, -33, 0, -33, 0, 0, -33, -33, -33, 0, 0, 0, 0, -33, -33, 0, 0,
        // State 58
        0, -23, 0, -23, -23, -23, 0, -23, 0, -23, 0, 0, -23, -23, -23, 0, 0, 0, 0, -23, -23, 0, 0,
    ];
    const __EOF_ACTION: &'static [i8] = &[
        // State 0
        0,
        // State 1
        -60,
        // State 2
        0,
        // State 3
        0,
        // State 4
        0,
        // State 5
        0,
        // State 6
        0,
        // State 7
        -38,
        // State 8
        0,
        // State 9
        0,
        // State 10
        0,
        // State 11
        0,
        // State 12
        0,
        // State 13
        0,
        // State 14
        0,
        // State 15
        0,
        // State 16
        0,
        // State 17
        0,
        // State 18
        0,
        // State 19
        0,
        // State 20
        0,
        // State 21
        0,
        // State 22
        0,
        // State 23
        0,
        // State 24
        0,
        // State 25
        0,
        // State 26
        0,
        // State 27
        0,
        // State 28
        0,
        // State 29
        0,
        // State 30
        0,
        // State 31
        0,
        // State 32
        0,
        // State 33
        0,
        // State 34
        0,
        // State 35
        0,
        // State 36
        0,
        // State 37
        0,
        // State 38
        0,
        // State 39
        0,
        // State 40
        0,
        // State 41
        0,
        // State 42
        0,
        // State 43
        0,
        // State 44
        0,
        // State 45
        0,
        // State 46
        0,
        // State 47
        0,
        // State 48
        0,
        // State 49
        0,
        // State 50
        0,
        // State 51
        0,
        // State 52
        0,
        // State 53
        0,
        // State 54
        0,
        // State 55
        0,
        // State 56
        0,
        // State 57
        0,
        // State 58
        0,
    ];
    const __GOTO: &'static [i8] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 2
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 7
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 8
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 15, 16, 0, 0, 17, 18, 19, 20, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 9
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 10
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 12
        0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 13
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 16
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 17
        0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 18
        0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 19
        0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 20
        0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0,
        // State 21
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 22
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 23
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 17, 0, 0, 0, 0, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 24
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 25
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 26
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 11, 12, 13, 14, 15, 16, 0, 0, 17, 18, 19, 20, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 27
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 28
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 29
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 30
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 32
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 14, 15, 16, 0, 0, 17, 0, 0, 20, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 33
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 36
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 37
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 12, 13, 14, 15, 16, 0, 0, 17, 0, 19, 20, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 38
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 39
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 40
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 13, 14, 15, 16, 0, 0, 17, 0, 0, 20, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 41
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 42
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 43
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 15, 16, 0, 0, 17, 0, 0, 0, 21, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 44
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 45
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 46
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 47
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 16, 0, 0, 17, 0, 0, 0, 0, 22, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 0, 0,
        // State 48
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 49
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 50
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 51
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 52
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 53
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 54
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 55
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 56
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 57
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 58
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    fn __expected_tokens(__state: usize) -> Vec<::std::string::String> {
        const __TERMINAL: &'static [&'static str] = &[
            r###""!""###,
            r###""&&""###,
            r###""(""###,
            r###"")""###,
            r###""*""###,
            r###""+""###,
            r###"",""###,
            r###""-""###,
            r###""->""###,
            r###""/""###,
            r###""/**@""###,
            r###"":""###,
            r###""<""###,
            r###"">""###,
            r###"">=""###,
            r###""@*/""###,
            r###""false""###,
            r###""true""###,
            r###""{""###,
            r###""||""###,
            r###""}""###,
            r###"r#"[0-9]+"#"###,
            r###"r#"[a-zA-Z][a-zA-Z0-9_]*"#"###,
        ];
        __ACTION[(__state * 23)..].iter().zip(__TERMINAL).filter_map(|(&state, terminal)| {
            if state == 0 {
                None
            } else {
                Some(terminal.to_string())
            }
        }).collect()
    }
    pub struct __StateMachine<'input, F>
    where F: Fn() -> ExprId, F: Copy
    {
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __phantom: ::std::marker::PhantomData<(&'input (), F)>,
    }
    impl<'input, F> __state_machine::ParserDefinition for __StateMachine<'input, F>
    where F: Fn() -> ExprId, F: Copy
    {
        type Location = usize;
        type Error = &'static str;
        type Token = Token<'input>;
        type TokenIndex = usize;
        type Symbol = __Symbol<'input>;
        type Success = Reft;
        type StateIndex = i8;
        type Action = i8;
        type ReduceIndex = i8;
        type NonterminalIndex = usize;

        #[inline]
        fn start_location(&self) -> Self::Location {
              Default::default()
        }

        #[inline]
        fn start_state(&self) -> Self::StateIndex {
              0
        }

        #[inline]
        fn token_to_index(&self, token: &Self::Token) -> Option<usize> {
            __token_to_integer(token, ::std::marker::PhantomData::<(&(), F)>)
        }

        #[inline]
        fn action(&self, state: i8, integer: usize) -> i8 {
            __ACTION[(state as usize) * 23 + integer]
        }

        #[inline]
        fn error_action(&self, state: i8) -> i8 {
            __ACTION[(state as usize) * 23 + (23 - 1)]
        }

        #[inline]
        fn eof_action(&self, state: i8) -> i8 {
            __EOF_ACTION[state as usize]
        }

        #[inline]
        fn goto(&self, state: i8, nt: usize) -> i8 {
            __GOTO[(state as usize) * 39 + nt] - 1
        }

        fn token_to_symbol(&self, token_index: usize, token: Self::Token) -> Self::Symbol {
            __token_to_symbol(token_index, token, ::std::marker::PhantomData::<(&(), F)>)
        }

        fn expected_tokens(&self, state: i8) -> Vec<String> {
            __expected_tokens(state as usize)
        }

        #[inline]
        fn uses_error_recovery(&self) -> bool {
            false
        }

        #[inline]
        fn error_recovery_symbol(
            &self,
            recovery: __state_machine::ErrorRecovery<Self>,
        ) -> Self::Symbol {
            panic!("error recovery not enabled for this grammar")
        }

        fn reduce(
            &mut self,
            action: i8,
            start_location: Option<&Self::Location>,
            states: &mut Vec<i8>,
            symbols: &mut Vec<__state_machine::SymbolTriple<Self>>,
        ) -> Option<__state_machine::ParseResult<Self>> {
            __reduce(
                self.offset,
                self.ctxt,
                self.next_expr_id,
                self.input,
                action,
                start_location,
                states,
                symbols,
                ::std::marker::PhantomData::<(&(), F)>,
            )
        }

        fn simulate_reduce(&self, action: i8) -> __state_machine::SimulatedReduce<Self> {
            __simulate_reduce(action, ::std::marker::PhantomData::<(&(), F)>)
        }
    }
    fn __token_to_integer<
        'input,
        F,
    >(
        __token: &Token<'input>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> Option<usize>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match *__token {
            Token(2, _) if true => Some(0),
            Token(3, _) if true => Some(1),
            Token(4, _) if true => Some(2),
            Token(5, _) if true => Some(3),
            Token(6, _) if true => Some(4),
            Token(7, _) if true => Some(5),
            Token(8, _) if true => Some(6),
            Token(9, _) if true => Some(7),
            Token(10, _) if true => Some(8),
            Token(11, _) if true => Some(9),
            Token(12, _) if true => Some(10),
            Token(13, _) if true => Some(11),
            Token(14, _) if true => Some(12),
            Token(15, _) if true => Some(13),
            Token(16, _) if true => Some(14),
            Token(17, _) if true => Some(15),
            Token(18, _) if true => Some(16),
            Token(19, _) if true => Some(17),
            Token(20, _) if true => Some(18),
            Token(21, _) if true => Some(19),
            Token(22, _) if true => Some(20),
            Token(0, _) if true => Some(21),
            Token(1, _) if true => Some(22),
            _ => None,
        }
    }
    fn __token_to_symbol<
        'input,
        F,
    >(
        __token_index: usize,
        __token: Token<'input>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> __Symbol<'input>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match __token_index {
            0 => match __token {
                Token(2, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            1 => match __token {
                Token(3, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            2 => match __token {
                Token(4, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            3 => match __token {
                Token(5, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            4 => match __token {
                Token(6, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            5 => match __token {
                Token(7, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            6 => match __token {
                Token(8, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            7 => match __token {
                Token(9, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            8 => match __token {
                Token(10, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            9 => match __token {
                Token(11, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            10 => match __token {
                Token(12, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            11 => match __token {
                Token(13, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            12 => match __token {
                Token(14, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            13 => match __token {
                Token(15, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            14 => match __token {
                Token(16, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            15 => match __token {
                Token(17, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            16 => match __token {
                Token(18, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            17 => match __token {
                Token(19, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            18 => match __token {
                Token(20, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            19 => match __token {
                Token(21, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            20 => match __token {
                Token(22, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            21 => match __token {
                Token(0, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            22 => match __token {
                Token(1, __tok0) => __Symbol::Variant0((__tok0)),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
    fn __simulate_reduce<
        'input,
        F,
    >(
        __reduce_index: i8,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> __state_machine::SimulatedReduce<__StateMachine<'input, F>>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        match __reduce_index {
            0 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 0,
                }
            }
            1 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 1,
                }
            }
            2 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 1,
                }
            }
            3 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 2,
                }
            }
            4 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 2,
                }
            }
            5 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 3,
                }
            }
            6 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 4,
                }
            }
            7 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 5,
                }
            }
            8 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 6,
                }
            }
            9 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 7,
                }
            }
            10 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 8,
                }
            }
            11 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 9,
                }
            }
            12 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 10,
                }
            }
            13 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 11,
                }
            }
            14 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 12,
                }
            }
            15 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 12,
                }
            }
            16 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 13,
                }
            }
            17 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 14,
                }
            }
            18 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 15,
                }
            }
            19 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 15,
                }
            }
            20 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 16,
                }
            }
            21 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 16,
                }
            }
            22 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 16,
                }
            }
            23 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 17,
                }
            }
            24 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 5,
                    nonterminal_produced: 18,
                }
            }
            25 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 19,
                }
            }
            26 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 20,
                }
            }
            27 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 20,
                }
            }
            28 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 21,
                }
            }
            29 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 21,
                }
            }
            30 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 22,
                }
            }
            31 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 22,
                }
            }
            32 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 23,
                }
            }
            33 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 23,
                }
            }
            34 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            35 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            36 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 24,
                }
            }
            37 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 3,
                    nonterminal_produced: 25,
                }
            }
            38 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 26,
                }
            }
            39 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 27,
                }
            }
            40 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 28,
                }
            }
            41 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            42 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            43 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 29,
                }
            }
            44 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 30,
                }
            }
            45 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 30,
                }
            }
            46 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 31,
                }
            }
            47 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 31,
                }
            }
            48 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 5,
                    nonterminal_produced: 32,
                }
            }
            49 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 33,
                }
            }
            50 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 33,
                }
            }
            51 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 34,
                }
            }
            52 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 0,
                    nonterminal_produced: 34,
                }
            }
            53 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 2,
                    nonterminal_produced: 34,
                }
            }
            54 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 34,
                }
            }
            55 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 35,
                }
            }
            56 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 36,
                }
            }
            57 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 36,
                }
            }
            58 => {
                __state_machine::SimulatedReduce::Reduce {
                    states_to_pop: 1,
                    nonterminal_produced: 37,
                }
            }
            59 => __state_machine::SimulatedReduce::Accept,
            _ => panic!("invalid reduction index {}", __reduce_index)
        }
    }
    pub struct LocalAnnotParser {
        builder: super::__intern_token::__MatcherBuilder,
        _priv: (),
    }

    impl LocalAnnotParser {
        pub fn new() -> LocalAnnotParser {
            let __builder = super::__intern_token::__MatcherBuilder::new();
            LocalAnnotParser {
                builder: __builder,
                _priv: (),
            }
        }

        #[allow(dead_code)]
        pub fn parse<
            'input,
            F,
        >(
            &self,
            offset: BytePos,
            ctxt: SyntaxContext,
            next_expr_id: F,
            input: &'input str,
        ) -> Result<Reft, __lalrpop_util::ParseError<usize, Token<'input>, &'static str>>
        where
            F: Fn() -> ExprId,
            F: Copy,
        {
            let mut __tokens = self.builder.matcher(input);
            let __r = __state_machine::Parser::drive(
                __StateMachine {
                    offset,
                    ctxt,
                    next_expr_id,
                    input,
                    __phantom: ::std::marker::PhantomData::<(&(), F)>,
                },
                __tokens,
            );
            __r
        }
    }
    pub(crate) fn __reduce<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> Option<Result<Reft,__lalrpop_util::ParseError<usize, Token<'input>, &'static str>>>
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        let (__pop_states, __nonterminal) = match __action {
            0 => {
                __reduce0(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            1 => {
                __reduce1(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            2 => {
                __reduce2(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            3 => {
                __reduce3(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            4 => {
                __reduce4(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            5 => {
                __reduce5(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            6 => {
                __reduce6(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            7 => {
                __reduce7(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            8 => {
                __reduce8(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            9 => {
                __reduce9(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            10 => {
                __reduce10(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            11 => {
                __reduce11(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            12 => {
                __reduce12(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            13 => {
                __reduce13(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            14 => {
                __reduce14(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            15 => {
                __reduce15(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            16 => {
                __reduce16(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            17 => {
                __reduce17(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            18 => {
                __reduce18(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            19 => {
                __reduce19(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            20 => {
                __reduce20(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            21 => {
                __reduce21(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            22 => {
                __reduce22(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            23 => {
                __reduce23(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            24 => {
                __reduce24(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            25 => {
                __reduce25(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            26 => {
                __reduce26(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            27 => {
                __reduce27(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            28 => {
                __reduce28(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            29 => {
                __reduce29(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            30 => {
                __reduce30(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            31 => {
                __reduce31(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            32 => {
                __reduce32(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            33 => {
                __reduce33(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            34 => {
                __reduce34(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            35 => {
                __reduce35(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            36 => {
                __reduce36(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            37 => {
                __reduce37(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            38 => {
                __reduce38(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            39 => {
                __reduce39(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            40 => {
                __reduce40(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            41 => {
                __reduce41(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            42 => {
                __reduce42(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            43 => {
                __reduce43(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            44 => {
                __reduce44(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            45 => {
                __reduce45(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            46 => {
                __reduce46(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            47 => {
                __reduce47(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            48 => {
                __reduce48(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            49 => {
                __reduce49(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            50 => {
                __reduce50(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            51 => {
                __reduce51(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            52 => {
                __reduce52(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            53 => {
                __reduce53(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            54 => {
                __reduce54(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            55 => {
                __reduce55(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            56 => {
                __reduce56(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            57 => {
                __reduce57(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            58 => {
                __reduce58(offset, ctxt, next_expr_id, input, __action, __lookahead_start, __states, __symbols, ::std::marker::PhantomData::<(&(), F)>)
            }
            59 => {
                // __LocalAnnot = LocalAnnot => ActionFn(1);
                let __sym0 = __pop_Variant1(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action1::<F>(offset, ctxt, next_expr_id, input, __sym0);
                return Some(Ok(__nt));
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __states_len = __states.len();
        __states.truncate(__states_len - __pop_states);
        let __state = *__states.last().unwrap() as usize;
        let __next_state = __GOTO[__state * 39 + __nonterminal] - 1;
        __states.push(__next_state);
        None
    }
    fn __pop_Variant4<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, BinOp, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant4(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant10<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, BinOpKind, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant10(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant5<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Box<Pred>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant5(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant6<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, FnType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant6(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant7<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Ident, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant7(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant8<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Lit, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant8(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant9<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Name, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant9(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant1<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Reft, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant1(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant13<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, UnOp, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant13(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant14<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, UnOpKind, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant14(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant12<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Vec<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant12(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant3<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, usize, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant3(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant11<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::option::Option<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant11(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant2<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Reft>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant2(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Variant0<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant0(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    pub(crate) fn __reduce0<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",") = Reft, "," => ActionFn(50);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action50::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (2, 0)
    }
    pub(crate) fn __reduce1<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")* =  => ActionFn(48);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action48::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (0, 1)
    }
    pub(crate) fn __reduce2<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")* = (<Reft> ",")+ => ActionFn(49);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action49::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 1)
    }
    pub(crate) fn __reduce3<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")+ = Reft, "," => ActionFn(57);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action57::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (2, 2)
    }
    pub(crate) fn __reduce4<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // (<Reft> ",")+ = (<Reft> ",")+, Reft, "," => ActionFn(58);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action58::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (3, 2)
    }
    pub(crate) fn __reduce5<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // @L =  => ActionFn(45);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action45::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 3)
    }
    pub(crate) fn __reduce6<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // @R =  => ActionFn(44);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action44::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 4)
    }
    pub(crate) fn __reduce7<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup1> = OpGroup1 => ActionFn(80);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action80::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 5)
    }
    pub(crate) fn __reduce8<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup2> = OpGroup2 => ActionFn(81);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action81::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 6)
    }
    pub(crate) fn __reduce9<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup3> = OpGroup3 => ActionFn(82);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action82::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 7)
    }
    pub(crate) fn __reduce10<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup4> = OpGroup4 => ActionFn(83);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action83::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 8)
    }
    pub(crate) fn __reduce11<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // BinOp<OpGroup5> = OpGroup5 => ActionFn(84);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action84::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 9)
    }
    pub(crate) fn __reduce12<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel1 = LeftAssoc<OpGroup1, ExprLevel2> => ActionFn(7);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action7::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 10)
    }
    pub(crate) fn __reduce13<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel2 = LeftAssoc<OpGroup2, ExprLevel3> => ActionFn(8);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action8::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 11)
    }
    pub(crate) fn __reduce14<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel3 = ExprLevel4, BinOp<OpGroup3>, ExprLevel4 => ActionFn(85);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action85::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 12)
    }
    pub(crate) fn __reduce15<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel3 = ExprLevel4 => ActionFn(10);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action10::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 12)
    }
    pub(crate) fn __reduce16<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel4 = LeftAssoc<OpGroup4, ExprLevel5> => ActionFn(11);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action11::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 13)
    }
    pub(crate) fn __reduce17<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel5 = LeftAssoc<OpGroup5, ExprLevel6> => ActionFn(12);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action12::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 14)
    }
    pub(crate) fn __reduce18<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel6 = UnOp, ExprLevel7 => ActionFn(86);
        let __sym1 = __pop_Variant5(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action86::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 15)
    }
    pub(crate) fn __reduce19<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel6 = ExprLevel7 => ActionFn(14);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action14::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 15)
    }
    pub(crate) fn __reduce20<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = Name => ActionFn(87);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action87::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 16)
    }
    pub(crate) fn __reduce21<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = Lit => ActionFn(88);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action88::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 16)
    }
    pub(crate) fn __reduce22<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ExprLevel7 = "(", ExprLevel1, ")" => ActionFn(17);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant5(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action17::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 16)
    }
    pub(crate) fn __reduce23<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // FnAnnot = "/**@", FnType, "@*/" => ActionFn(2);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action2::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 17)
    }
    pub(crate) fn __reduce24<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // FnType = "(", ReftList, ")", "->", Reft => ActionFn(3);
        let __sym4 = __pop_Variant1(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym4.2.clone();
        let __nt = super::__action3::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2, __sym3, __sym4);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (5, 18)
    }
    pub(crate) fn __reduce25<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Ident = r#"[a-zA-Z][a-zA-Z0-9_]*"# => ActionFn(89);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action89::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (1, 19)
    }
    pub(crate) fn __reduce26<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup1, ExprLevel2> = LeftAssoc<OpGroup1, ExprLevel2>, BinOp<OpGroup1>, ExprLevel2 => ActionFn(90);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action90::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 20)
    }
    pub(crate) fn __reduce27<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup1, ExprLevel2> = ExprLevel2 => ActionFn(43);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action43::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 20)
    }
    pub(crate) fn __reduce28<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup2, ExprLevel3> = LeftAssoc<OpGroup2, ExprLevel3>, BinOp<OpGroup2>, ExprLevel3 => ActionFn(91);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action91::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 21)
    }
    pub(crate) fn __reduce29<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup2, ExprLevel3> = ExprLevel3 => ActionFn(41);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action41::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 21)
    }
    pub(crate) fn __reduce30<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup4, ExprLevel5> = LeftAssoc<OpGroup4, ExprLevel5>, BinOp<OpGroup4>, ExprLevel5 => ActionFn(92);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action92::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 22)
    }
    pub(crate) fn __reduce31<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup4, ExprLevel5> = ExprLevel5 => ActionFn(38);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action38::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 22)
    }
    pub(crate) fn __reduce32<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup5, ExprLevel6> = LeftAssoc<OpGroup5, ExprLevel6>, BinOp<OpGroup5>, ExprLevel6 => ActionFn(93);
        let __sym2 = __pop_Variant5(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action93::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 23)
    }
    pub(crate) fn __reduce33<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LeftAssoc<OpGroup5, ExprLevel6> = ExprLevel6 => ActionFn(36);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action36::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 23)
    }
    pub(crate) fn __reduce34<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = r#"[0-9]+"# => ActionFn(94);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action94::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce35<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = "true" => ActionFn(95);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action95::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce36<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Lit = "false" => ActionFn(96);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action96::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (1, 24)
    }
    pub(crate) fn __reduce37<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // LocalAnnot = "/**@", Reft, "@*/" => ActionFn(4);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action4::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce38<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Name = Ident => ActionFn(32);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action32::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (1, 26)
    }
    pub(crate) fn __reduce39<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup1 = "||" => ActionFn(18);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action18::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 27)
    }
    pub(crate) fn __reduce40<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup2 = "&&" => ActionFn(19);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action19::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce41<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = "<" => ActionFn(20);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action20::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce42<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = ">" => ActionFn(21);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action21::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce43<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup3 = ">=" => ActionFn(22);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action22::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce44<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup4 = "+" => ActionFn(23);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action23::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce45<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup4 = "-" => ActionFn(24);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action24::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce46<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup5 = "*" => ActionFn(25);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action25::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce47<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // OpGroup5 = "/" => ActionFn(26);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action26::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce48<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft = Ident, ":", "{", ExprLevel1, "}" => ActionFn(97);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant5(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym4.2.clone();
        let __nt = super::__action97::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1, __sym2, __sym3, __sym4);
        __symbols.push((__start, __Symbol::Variant1(__nt), __end));
        (5, 32)
    }
    pub(crate) fn __reduce49<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft? = Reft => ActionFn(46);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action46::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (1, 33)
    }
    pub(crate) fn __reduce50<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // Reft? =  => ActionFn(47);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action47::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (0, 33)
    }
    pub(crate) fn __reduce51<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = Reft => ActionFn(99);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action99::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce52<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList =  => ActionFn(100);
        let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
        let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
        let __nt = super::__action100::<F>(offset, ctxt, next_expr_id, input, &__start, &__end);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (0, 34)
    }
    pub(crate) fn __reduce53<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = (<Reft> ",")+, Reft => ActionFn(101);
        let __sym1 = __pop_Variant1(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action101::<F>(offset, ctxt, next_expr_id, input, __sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (2, 34)
    }
    pub(crate) fn __reduce54<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // ReftList = (<Reft> ",")+ => ActionFn(102);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action102::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce55<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOp = UnOpKind => ActionFn(98);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action98::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (1, 35)
    }
    pub(crate) fn __reduce56<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOpKind = "!" => ActionFn(27);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action27::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 36)
    }
    pub(crate) fn __reduce57<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // UnOpKind = "*" => ActionFn(28);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action28::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 36)
    }
    pub(crate) fn __reduce58<
        'input,
        F,
    >(
        offset: BytePos,
        ctxt: SyntaxContext,
        next_expr_id: F,
        input: &'input str,
        __action: i8,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i8>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<(&'input (), F)>,
    ) -> (usize, usize)
    where
        F: Fn() -> ExprId,
        F: Copy,
    {
        // __FnAnnot = FnAnnot => ActionFn(0);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action0::<F>(offset, ctxt, next_expr_id, input, __sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 37)
    }
}
pub use self::__parse__LocalAnnot::LocalAnnotParser;
#[cfg_attr(rustfmt, rustfmt_skip)]
mod __intern_token {
    #![allow(unused_imports)]
    use std::str::FromStr;
    use super::span_with_offset;
    use crate::syntax::ast::*;
    use rustc_span::{symbol::Symbol, hygiene::SyntaxContext, BytePos};
    #[allow(unused_extern_crates)]
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(unused_imports)]
    use self::__lalrpop_util::state_machine as __state_machine;
    extern crate regex as __regex;
    use std::fmt as __fmt;

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Token<'input>(pub usize, pub &'input str);
    impl<'a> __fmt::Display for Token<'a> {
        fn fmt<'f>(&self, formatter: &mut __fmt::Formatter<'f>) -> Result<(), __fmt::Error> {
            __fmt::Display::fmt(self.1, formatter)
        }
    }

    pub struct __MatcherBuilder {
        regex_set: __regex::RegexSet,
        regex_vec: Vec<__regex::Regex>,
    }

    impl __MatcherBuilder {
        pub fn new() -> __MatcherBuilder {
            let __strs: &[&str] = &[
                "^([0-9]+)",
                "^([A-Za-z][0-9A-Z_a-z]*)",
                "^(!)",
                "^(\\&\\&)",
                "^(\\()",
                "^(\\))",
                "^(\\*)",
                "^(\\+)",
                "^(,)",
                "^(\\-)",
                "^(\\->)",
                "^(/)",
                "^(/\\*\\*@)",
                "^(:)",
                "^(<)",
                "^(>)",
                "^(>=)",
                "^(@\\*/)",
                "^(false)",
                "^(true)",
                "^(\\{)",
                "^(\\|\\|)",
                "^(\\})",
            ];
            let __regex_set = __regex::RegexSet::new(__strs).unwrap();
            let __regex_vec = vec![
                __regex::Regex::new("^([0-9]+)").unwrap(),
                __regex::Regex::new("^([A-Za-z][0-9A-Z_a-z]*)").unwrap(),
                __regex::Regex::new("^(!)").unwrap(),
                __regex::Regex::new("^(\\&\\&)").unwrap(),
                __regex::Regex::new("^(\\()").unwrap(),
                __regex::Regex::new("^(\\))").unwrap(),
                __regex::Regex::new("^(\\*)").unwrap(),
                __regex::Regex::new("^(\\+)").unwrap(),
                __regex::Regex::new("^(,)").unwrap(),
                __regex::Regex::new("^(\\-)").unwrap(),
                __regex::Regex::new("^(\\->)").unwrap(),
                __regex::Regex::new("^(/)").unwrap(),
                __regex::Regex::new("^(/\\*\\*@)").unwrap(),
                __regex::Regex::new("^(:)").unwrap(),
                __regex::Regex::new("^(<)").unwrap(),
                __regex::Regex::new("^(>)").unwrap(),
                __regex::Regex::new("^(>=)").unwrap(),
                __regex::Regex::new("^(@\\*/)").unwrap(),
                __regex::Regex::new("^(false)").unwrap(),
                __regex::Regex::new("^(true)").unwrap(),
                __regex::Regex::new("^(\\{)").unwrap(),
                __regex::Regex::new("^(\\|\\|)").unwrap(),
                __regex::Regex::new("^(\\})").unwrap(),
            ];
            __MatcherBuilder { regex_set: __regex_set, regex_vec: __regex_vec }
        }
        pub fn matcher<'input, 'builder>(&'builder self, s: &'input str) -> __Matcher<'input, 'builder> {
            __Matcher {
                text: s,
                consumed: 0,
                regex_set: &self.regex_set,
                regex_vec: &self.regex_vec,
            }
        }
    }

    pub struct __Matcher<'input, 'builder> {
        text: &'input str,
        consumed: usize,
        regex_set: &'builder __regex::RegexSet,
        regex_vec: &'builder Vec<__regex::Regex>,
    }

    impl<'input, 'builder> Iterator for __Matcher<'input, 'builder> {
        type Item = Result<(usize, Token<'input>, usize), __lalrpop_util::ParseError<usize,Token<'input>,&'static str>>;

        fn next(&mut self) -> Option<Self::Item> {
            let __text = self.text.trim_start();
            let __whitespace = self.text.len() - __text.len();
            let __start_offset = self.consumed + __whitespace;
            if __text.is_empty() {
                self.text = __text;
                self.consumed = __start_offset;
                None
            } else {
                let __matches = self.regex_set.matches(__text);
                if !__matches.matched_any() {
                    Some(Err(__lalrpop_util::ParseError::InvalidToken {
                        location: __start_offset,
                    }))
                } else {
                    let mut __longest_match = 0;
                    let mut __index = 0;
                    for __i in 0 .. 23 {
                        if __matches.matched(__i) {
                            let __match = self.regex_vec[__i].find(__text).unwrap();
                            let __len = __match.end();
                            if __len >= __longest_match {
                                __longest_match = __len;
                                __index = __i;
                            }
                        }
                    }
                    let __result = &__text[..__longest_match];
                    let __remaining = &__text[__longest_match..];
                    let __end_offset = __start_offset + __longest_match;
                    self.text = __remaining;
                    self.consumed = __end_offset;
                    Some(Ok((__start_offset, Token(__index, __result), __end_offset)))
                }
            }
        }
    }
}
pub use self::__intern_token::Token;

#[allow(unused_variables)]
fn __action0<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, FnType, usize),
) -> FnType
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action1<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Reft, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action2<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, __0, _): (usize, FnType, usize),
    (_, _, _): (usize, &'input str, usize),
) -> FnType
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action3<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, inputs, _): (usize, Vec<Reft>, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, output, _): (usize, Reft, usize),
) -> FnType
where
    F: Fn() -> ExprId,
    F: Copy,
{
    FnType {
            inputs: inputs,
            output
        }
}

#[allow(unused_variables)]
fn __action4<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, __0, _): (usize, Reft, usize),
    (_, _, _): (usize, &'input str, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action5<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, refines, _): (usize, ::std::vec::Vec<Reft>, usize),
    (_, r, _): (usize, ::std::option::Option<Reft>, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    {
        let mut refines = refines;
        if let Some(r) = r {
            refines.push(r);
        }
        refines
    }
}

#[allow(unused_variables)]
fn __action6<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, ident, _): (usize, Ident, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, e, _): (usize, Box<Pred>, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, hi, _): (usize, usize, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Reft {
            binding: ident,
            pred: *e,
            span: span_with_offset(lo, hi, offset, ctxt),
            hir_res: HirRes::Unresolved
        }
}

#[allow(unused_variables)]
fn __action7<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action8<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action9<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, e1, _): (usize, Box<Pred>, usize),
    (_, op, _): (usize, BinOp, usize),
    (_, e2, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Binary(e1, op, e2),
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action10<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action11<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action12<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action13<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, op, _): (usize, UnOp, usize),
    (_, e, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Unary(op, e),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action14<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action15<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, name, _): (usize, Name, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Name(name),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action16<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, lit, _): (usize, Lit, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Lit(lit),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action17<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, __0, _): (usize, Box<Pred>, usize),
    (_, _, _): (usize, &'input str, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action18<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Or
}

#[allow(unused_variables)]
fn __action19<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::And
}

#[allow(unused_variables)]
fn __action20<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Lt
}

#[allow(unused_variables)]
fn __action21<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Gt
}

#[allow(unused_variables)]
fn __action22<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Ge
}

#[allow(unused_variables)]
fn __action23<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Add
}

#[allow(unused_variables)]
fn __action24<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Sub
}

#[allow(unused_variables)]
fn __action25<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Mul
}

#[allow(unused_variables)]
fn __action26<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> BinOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOpKind::Div
}

#[allow(unused_variables)]
fn __action27<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> UnOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    UnOpKind::Not
}

#[allow(unused_variables)]
fn __action28<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> UnOpKind
where
    F: Fn() -> ExprId,
    F: Copy,
{
    UnOpKind::Deref
}

#[allow(unused_variables)]
fn __action29<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, tok, _): (usize, &'input str, usize),
    (_, hi, _): (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    {
      let kind = match u128::from_str(tok) {
          Ok(i) => LitKind::Int(i, LitIntType::Unsuffixed),
          Err(_) => LitKind::Err(Symbol::intern(tok))
      };
      Lit { node: kind, span: span_with_offset(lo, hi, offset, ctxt) }
  }
}

#[allow(unused_variables)]
fn __action30<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, tok, _): (usize, &'input str, usize),
    (_, hi, _): (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Lit { node: LitKind::Bool(true), span: span_with_offset(lo, hi, offset, ctxt) }
}

#[allow(unused_variables)]
fn __action31<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, tok, _): (usize, &'input str, usize),
    (_, hi, _): (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Lit { node: LitKind::Bool(false), span: span_with_offset(lo, hi, offset, ctxt) }
}

#[allow(unused_variables)]
fn __action32<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Ident, usize),
) -> Name
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Name {ident: __0, hir_res: HirRes::Unresolved }
}

#[allow(unused_variables)]
fn __action33<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, sym, _): (usize, &'input str, usize),
    (_, hi, _): (usize, usize, usize),
) -> Ident
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Ident {
        name: Symbol::intern(sym),
        span: span_with_offset(lo, hi, offset, ctxt),
    }
}

#[allow(unused_variables)]
fn __action34<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, UnOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> UnOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    UnOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action35<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, e1, _): (usize, Box<Pred>, usize),
    (_, op, _): (usize, BinOp, usize),
    (_, e2, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Binary(e1, op, e2),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action36<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action37<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, e1, _): (usize, Box<Pred>, usize),
    (_, op, _): (usize, BinOp, usize),
    (_, e2, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Binary(e1, op, e2),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action38<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action39<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, BinOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action40<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, e1, _): (usize, Box<Pred>, usize),
    (_, op, _): (usize, BinOp, usize),
    (_, e2, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Binary(e1, op, e2),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action41<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action42<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, e1, _): (usize, Box<Pred>, usize),
    (_, op, _): (usize, BinOp, usize),
    (_, e2, _): (usize, Box<Pred>, usize),
    (_, hi, _): (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    box Pred {
            expr_id: next_expr_id(),
            kind: ExprKind::Binary(e1, op, e2),
            span: span_with_offset(lo, hi, offset, ctxt)
        }
}

#[allow(unused_variables)]
fn __action43<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action44<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> usize
where
    F: Fn() -> ExprId,
    F: Copy,
{
    __lookbehind.clone()
}

#[allow(unused_variables)]
fn __action45<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> usize
where
    F: Fn() -> ExprId,
    F: Copy,
{
    __lookahead.clone()
}

#[allow(unused_variables)]
fn __action46<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Reft, usize),
) -> ::std::option::Option<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    Some(__0)
}

#[allow(unused_variables)]
fn __action47<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    None
}

#[allow(unused_variables)]
fn __action48<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    vec![]
}

#[allow(unused_variables)]
fn __action49<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Reft>, usize),
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    v
}

#[allow(unused_variables)]
fn __action50<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Reft, usize),
    (_, _, _): (usize, &'input str, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    (__0)
}

#[allow(unused_variables)]
fn __action51<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, __0, _): (usize, Reft, usize),
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    vec![__0]
}

#[allow(unused_variables)]
fn __action52<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Reft>, usize),
    (_, e, _): (usize, Reft, usize),
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    { let mut v = v; v.push(e); v }
}

#[allow(unused_variables)]
fn __action53<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, BinOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action54<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, BinOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action55<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, BinOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action56<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    (_, lo, _): (usize, usize, usize),
    (_, kind, _): (usize, BinOpKind, usize),
    (_, hi, _): (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    BinOp {
            kind: kind,
            span: span_with_offset(lo, hi, offset, ctxt),
        }
}

#[allow(unused_variables)]
fn __action57<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Reft, usize),
    __1: (usize, &'input str, usize),
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action50::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action51::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action58<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Reft>, usize),
    __1: (usize, Reft, usize),
    __2: (usize, &'input str, usize),
) -> ::std::vec::Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action50::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action52::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action59<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, ::std::option::Option<Reft>, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action48::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action5::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
    )
}

#[allow(unused_variables)]
fn __action60<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Reft>, usize),
    __1: (usize, ::std::option::Option<Reft>, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action49::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action5::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action61<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
    __1: (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action53::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action62<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
    __1: (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action54::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action63<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
    __1: (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action39::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action64<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
    __1: (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action55::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action65<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
    __1: (usize, usize, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action56::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action66<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
    __3: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action9::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
fn __action67<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, UnOp, usize),
    __1: (usize, Box<Pred>, usize),
    __2: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action13::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
    )
}

#[allow(unused_variables)]
fn __action68<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Name, usize),
    __1: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action15::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action69<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Lit, usize),
    __1: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action16::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action70<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
    __1: (usize, usize, usize),
) -> Ident
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action33::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action71<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
    __3: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action42::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
fn __action72<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
    __3: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action40::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
fn __action73<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
    __3: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action37::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
fn __action74<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
    __3: (usize, usize, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action35::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
fn __action75<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
    __1: (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action29::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action76<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
    __1: (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action30::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action77<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
    __1: (usize, usize, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action31::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action78<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Ident, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, &'input str, usize),
    __3: (usize, Box<Pred>, usize),
    __4: (usize, &'input str, usize),
    __5: (usize, usize, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action6::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
        __2,
        __3,
        __4,
        __5,
    )
}

#[allow(unused_variables)]
fn __action79<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, UnOpKind, usize),
    __1: (usize, usize, usize),
) -> UnOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action45::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action34::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
        __0,
        __1,
    )
}

#[allow(unused_variables)]
fn __action80<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action61::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action81<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action62::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action82<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action63::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action83<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action64::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action84<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, BinOpKind, usize),
) -> BinOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action65::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action85<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action66::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action86<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, UnOp, usize),
    __1: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __1.2.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action67::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action87<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Name, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action68::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action88<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Lit, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action69::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action89<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
) -> Ident
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action70::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action90<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action71::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action91<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action72::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action92<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action73::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action93<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Box<Pred>, usize),
    __1: (usize, BinOp, usize),
    __2: (usize, Box<Pred>, usize),
) -> Box<Pred>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action74::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action94<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action75::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action95<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action76::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action96<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, &'input str, usize),
) -> Lit
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action77::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action97<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Ident, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, &'input str, usize),
    __3: (usize, Box<Pred>, usize),
    __4: (usize, &'input str, usize),
) -> Reft
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __4.2.clone();
    let __end0 = __4.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action78::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __1,
        __2,
        __3,
        __4,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action98<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, UnOpKind, usize),
) -> UnOp
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action44::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action79::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action99<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, Reft, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action46::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action59::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action100<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action47::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action59::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action101<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Reft>, usize),
    __1: (usize, Reft, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action46::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action60::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
fn __action102<
    'input,
    F,
>(
    offset: BytePos,
    ctxt: SyntaxContext,
    next_expr_id: F,
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Reft>, usize),
) -> Vec<Reft>
where
    F: Fn() -> ExprId,
    F: Copy,
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action47::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action60::<
    F,
    >(
        offset,
        ctxt,
        next_expr_id,
        input,
        __0,
        __temp0,
    )
}

pub trait __ToTriple<'input, F, > {
    fn to_triple(value: Self) -> Result<(usize,Token<'input>,usize), __lalrpop_util::ParseError<usize, Token<'input>, &'static str>>;
}

impl<'input, F, > __ToTriple<'input, F, > for (usize, Token<'input>, usize) {
    fn to_triple(value: Self) -> Result<(usize,Token<'input>,usize), __lalrpop_util::ParseError<usize, Token<'input>, &'static str>> {
        Ok(value)
    }
}
impl<'input, F, > __ToTriple<'input, F, > for Result<(usize, Token<'input>, usize), &'static str> {
    fn to_triple(value: Self) -> Result<(usize,Token<'input>,usize), __lalrpop_util::ParseError<usize, Token<'input>, &'static str>> {
        match value {
            Ok(v) => Ok(v),
            Err(error) => Err(__lalrpop_util::ParseError::User { error }),
        }
    }
}
