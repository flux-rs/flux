fn test_file(file: &str, expected: liquid_rust_fixpoint::Safeness) -> bool { 
    let s0:String = "target/debug/liquid-rust".to_string();
    let s1:String = "--crate-type=lib".to_string();
    let mut args: Vec<String> = vec!(s0, s1); 
    args.push(file.to_string());
    match liquid_rust_driver::run_compiler_result(args) {
        Ok(r) => r.tag == expected,
        _     => false,
    }
}

/// Test a single file that should be SAFE
#[allow(dead_code)]
pub fn test_safe(file: &str) -> bool {
    test_file(file, liquid_rust_fixpoint::Safeness::Safe)
}

/// Test a single file that should be UNSAFE
#[allow(dead_code)]
pub fn test_unsafe(file: &str) -> bool {
    test_file(file, liquid_rust_fixpoint::Safeness::Unsafe)
}

