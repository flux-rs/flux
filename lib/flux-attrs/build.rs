fn main() {
    // CODESYNC(build-sysroot, 5)
    println!("cargo:rerun-if-env-changed=FLUX_BUILD_SYSROOT");
    if std::env::var("FLUX_BUILD_SYSROOT").is_ok() {
        println!("cargo:rustc-cfg=flux_sysroot");
    }
}
