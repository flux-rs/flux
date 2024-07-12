#[flux::refined_by(p: int -> bool)]
struct S;

#[flux::sig(fn(S[@p]) -> S[p])]
fn ipa(x: S) -> S {
    x
}

#[flux::sig(fn[hrn p: int -> bool](S[|x| p(x) && x != 0]))]
fn ris(x: S) {}
