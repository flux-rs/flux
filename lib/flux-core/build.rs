fn main() {
    println!("cargo:rerun-if-env-changed=FLUX_SYSROOT_TEST");
    if std::env::var("FLUX_SYSROOT_TEST").is_ok() {
        println!("cargo:rustc-cfg=flux_sysroot_test");
    }
}
