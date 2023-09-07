#![feature(register_tool)]
#![register_tool(flux)]

use flux_rs::extern_spec;

#[extern_spec(std::string)]
#[flux::refined_by(len: int)]
struct String;

#[flux::sig(fn(String[@n]) requires n == 3)]
fn expect_string_len_3(s: String) {}

#[flux::sig(fn(String[3]))]
fn test_string_len_3(s: String) {
    expect_string_len_3(s);
}
