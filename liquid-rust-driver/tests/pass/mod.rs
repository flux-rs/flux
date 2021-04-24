macro_rules! pass_test {
    ($name:ident) => {
        #[test]
        fn $name() {
            let home = env!("RUSTUP_HOME");
            let toolchain = env!("RUSTUP_TOOLCHAIN");
            let sysroot = format!("--sysroot={}/toolchains/{}", home, toolchain);

            let path = concat!("tests/pass/", stringify!($name), ".rs");

            let code = liquid_rust_driver::run_compiler(vec![
                "whatever".into(),
                path.into(),
                sysroot.into(),
                "-O".into(),
                "--crate-type=lib".into(),
            ]);
            assert!(code == 0);
        }
    };
}

pass_test!(branches);
pass_test!(fun_call);
pass_test!(simple);
pass_test!(while_loop);
