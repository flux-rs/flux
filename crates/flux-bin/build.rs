use std::process::{Command, Output};

fn parse_output(output: Output) -> Option<String> {
    Some(String::from_utf8(output.stdout).ok()?.trim().to_string())
}

fn git_sha() -> Option<String> {
    parse_output(
        Command::new("git")
            .args(["describe", "--always", "--dirty=*"])
            .output()
            .ok()?,
    )
}

fn git_date() -> Option<String> {
    parse_output(
        Command::new("git")
            .args(["show", "-s", "--format=%cd", "--date=format:%Y-%m-%d", "HEAD"])
            .output()
            .ok()?,
    )
}

fn main() {
    if let Some(hash) = git_sha() {
        println!("cargo:rustc-env=GIT_SHA={}", hash);
    }
    if let Some(date) = git_date() {
        println!("cargo:rustc-env=GIT_DATE={}", date);
    }
}
