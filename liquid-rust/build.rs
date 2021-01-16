extern crate lalrpop;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    lalrpop::Configuration::new()
        .generate_in_source_tree()
        .process()
}
