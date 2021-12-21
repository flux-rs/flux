extern crate compiletest_rs as compiletest;

use std::path::PathBuf;

fn run_mode(mode: &'static str) {
    let mut config = compiletest::Config::default();
    config.mode = mode.parse().expect("Invalid mode");
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    config.link_deps(); // Populate config.target_rustcflags with dependencies on the path
    config.clean_rmeta(); // If your tests import the parent crate, this helps with E0464

    println!("biggity boggity {:?}", config.src_base);
    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    run_mode("run-pass");
    // run_mode("compile-fail");
}

pub fn test_file(file: &str, expected: liquid_rust_fixpoint::Safeness) -> bool {
    let s0: String = "liquid-rust".to_string();
    let s1: String = "--crate-type=lib".to_string();
    let mut args: Vec<String> = vec![s0, s1];
    args.push(file.to_string());
    match liquid_rust_driver::run_compiler_result(args) {
        Ok(r) => r.tag == expected,
        _ => false,
    }
}

#[macro_export]
macro_rules! tests {
    ($($name:ident: $file:literal => Safe),* $(,)?) => {$(
        #[test]
        fn $name() {
            assert!($crate::common::test_file(
                $file,
                liquid_rust_fixpoint::Safeness::Safe
            ));
        }
    )*};
    ($($name:ident: $file:literal => Unsafe),* $(,)?) => {$(
        #[test]
        fn $name() {
            assert!($crate::common::test_file(
                $file,
                liquid_rust_fixpoint::Safeness::Unsafe
            ));
        }
    )*};
}
