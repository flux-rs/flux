use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(b:bool)]
enum Option<T> {
    #[flux::variant(Option<T>[false])]
    None,
    #[flux::variant({T} -> Option<T>[true])]
    Some(T),
}
