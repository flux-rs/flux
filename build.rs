extern crate lalrpop;

fn main() {
    let _ = lalrpop::Configuration::new()
        .generate_in_source_tree()
        .process();
}
