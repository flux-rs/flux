macro_rules! fail_test {
    ($name:ident) => {
        #[test]
        fn $name() {
            let home = env!("RUSTUP_HOME");
            let toolchain = env!("RUSTUP_TOOLCHAIN");
            let sysroot = format!("--sysroot={}/toolchains/{}", home, toolchain);

            let path = concat!("tests/fail/", stringify!($name), ".rs");
            let code = liquid_rust_driver::run_compiler(vec![
                "whatever".into(),
                path.into(),
                sysroot.into(),
                "--crate-type=lib".into(),
            ]);
            assert!(code != 0);
        }
    };
}

fail_test!(one);
