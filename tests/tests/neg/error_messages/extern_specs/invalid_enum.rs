use flux_rs::attrs::*;

#[extern_spec]
enum Option<T> {
    //~^ ERROR invalid extern_spec
    Some(T),
}
