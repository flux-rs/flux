// Regression: generating weak kvars must query the resolved extern ID, not the
// local dummy item emitted by the extern_spec macro. Run with --suggestions.
use flux_attrs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct String;

#[extern_spec]
impl String {
    #[flux::sig(fn(&String[@n]) -> usize[n])]
    fn len(s: &String) -> usize;
}

#[flux::sig(fn(&String[@n]) -> usize[n])]
pub fn string_len(s: &String) -> usize {
    s.len()
}
