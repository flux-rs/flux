use flux_rs::extern_spec;

#[extern_spec(std::slice)]
#[flux::refined_by(len: int)]
struct Iter<'a, T>;

