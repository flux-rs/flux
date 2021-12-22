// extern crate compiletest_rs as compiletest;
// fn sysroot() -> Option<String> {
//     let home = option_env!("RUSTUP_HOME")?;
//     let toolchain = option_env!("RUSTUP_TOOLCHAIN")?;
//     Some(format!("{}/toolchains/{}/lib", home, toolchain))
// }
// fn run_mode(mode: &'static str) {
//     let mut config = compiletest::Config::default();
//     config.mode = mode.parse().expect("Invalid mode");
//     config.src_base = PathBuf::from(format!("tests/{}", mode));
//     config.link_deps(); // Populate config.target_rustcflags with dependencies on the path
//     config.clean_rmeta(); // If your tests import the parent crate, this helps with E0464
//     config.verbose = true; 
//     let ld_lib_path = "/Users/rjhala/.rustup/toolchains/nightly-2021-11-23-x86_64-apple-darwin/lib";
//     std::env::set_var("LD_LIBRARY_PATH", ld_lib_path);
//     let ld_lib= std::env::var("LD_LIBRARY_PATH");
//     println!("GET ld-lib-path = {:?}", ld_lib);
//     if let Some(path) = sysroot() {
//         println!("compile-test-paths [1]: path = {}", path);
//         config.compile_lib_path = PathBuf::from(&path);
//         config.run_lib_path = PathBuf::from(&path);
//     }
//     // config.rustc_path = ["target","debug","liquid-rust"].iter().collect(); // TODO: test
//     config.rustc_path = PathBuf::from("/Users/rjhala/research/rust/liquid-rust/target/debug/liquid-rust");
//     // config.target_rustcflags = Some("-L target/debug".to_string());
//     config.target_rustcflags = Some(format!(
//         "--crate-type=lib"
//         // "--emit=metadata -Dwarnings -Zui-testing -L dependency={}{}{}",
//         // deps_path.display(),
//         // host_libs,
//         // extern_flags(),
//     ));
//     println!("biggity boggity {:?}", config.src_base);
//     // if let Some(path) = option_env!("RUSTC_LIB_PATH") {
//     //     println!("compile-test-paths [2]: path = {}", path);
//     //     let path = PathBuf::from(path);
//     //     config.run_lib_path = path.clone();
//     //     config.compile_lib_path = path;
//     // }
//     let current_exe_path = std::env::current_exe().unwrap();
//     let deps_path = current_exe_path.parent().unwrap();
//     let profile_path = deps_path.parent().unwrap();
//     println!("compile-test-paths: exe = {:?}, deps = {:?}, profile = {:?}", current_exe_path, deps_path, profile_path);
//     compiletest::run_tests(&config);
// }
// #[test]
// fn compile_test() {
//     // let test = "/Users/rjhala/research/rust/liquid-rust/tests/pos/test00.rs";
//     let test = "/Users/rjhala/research/rust/liquid-rust/tests/pos/test00.rs";
//     test_file_exec(test, true);
//     // run_mode("run-pass");
//     // run_mode("compile-fail");
// }
// pub fn test_file(file: &str, expected: liquid_rust_fixpoint::Safeness) -> bool {
//     let s0: String = "liquid-rust".to_string();
//     let s1: String = "--crate-type=lib".to_string();
//     let mut args: Vec<String> = vec![s0, s1];
//     args.push(file.to_string());
//     match liquid_rust_driver::run_compiler_result(args) {
//         Ok(r) => r.tag == expected,
//         _ => false,
//     }
// }

pub fn test_file_exec(file: &str, expected: bool) {
    let mut lr = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    lr.push("../target/debug/liquid-rust");

    let res = std::process::Command::new(lr)
        .arg("--crate-type=lib")
        .arg(file)
        .status()
        .expect("failed to execute process");
    assert_eq!(res.success(), expected); 
}

#[macro_export]
macro_rules! tests {
    ($($name:ident: $file:literal => Safe),* $(,)?) => {$(
        #[test]
        fn $name() {
            $crate::common::test_file_exec($file, true)
        }
    )*};
    ($($name:ident: $file:literal => Unsafe),* $(,)?) => {$(
        #[test]
        fn $name() {
            $crate::common::test_file_exec($file, false)
        }
    )*};
}
