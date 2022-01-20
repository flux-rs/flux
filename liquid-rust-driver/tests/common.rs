pub fn test_file_exec(file: &str, expected: bool) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let mut lr = root.clone();
    lr.push("../target/debug/liquid-rust");

    let mut test_path = root.clone();
    test_path.push(file);

    let res = std::process::Command::new(lr)
        .arg("--crate-type=lib")
        .arg(test_path)
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
