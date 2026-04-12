use flux_attrs::extern_spec;

#[extern_spec(std::slice)]
#[flux::refined_by(len: int)]
struct Iter<'a, T>;

