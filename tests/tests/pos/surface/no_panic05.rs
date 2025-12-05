#[flux::no_panic]
fn run_closure(f: impl Fn()) {
    f();
}

fn main() {
    run_closure(
        #[flux::no_panic]
        || {
            let x = 10;
        },
    );
}