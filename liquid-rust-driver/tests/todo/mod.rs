macro_rules! todo_test {
    ($name:ident) => {
        #[test]
        #[should_panic]
        fn $name() {
            let home = env!("RUSTUP_HOME");
            let toolchain = env!("RUSTUP_TOOLCHAIN");
            let sysroot = format!("--sysroot={}/toolchains/{}", home, toolchain);

            let path = concat!("tests/todo/", stringify!($name), ".rs");

            liquid_rust_driver::run_compiler(vec![
                "whatever".into(),
                "-Znll-facts".into(),
                path.into(),
                sysroot.into(),
                "--crate-type=lib".into(),
            ]);
        }
    };
}

todo_test!(array);
