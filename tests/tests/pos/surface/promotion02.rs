use std::fmt;

fn print_formatted(args: fmt::Arguments) {
    println!("{}", args);
}

pub fn test() {
    print_formatted(format_args!("Hello, {}!", "world"));

    let pi = 3.14159;
    print_formatted(format_args!("Pi is approximately {:.2}", pi));
}
