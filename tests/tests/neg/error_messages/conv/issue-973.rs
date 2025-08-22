extern crate flux_rs;

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int)]
pub struct Graph(Vec<[Edge; 2]>);

#[flux_rs::alias(type Edge(lim: int) = usize{ x: x <= lim })]
type Edge = usize;

impl Graph {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg Graph[@n], [Edge[n]; 2]) ensures self: Graph[n + 1])] //~ ERROR type alias takes 1 generic refinement argument
    pub fn push(&mut self, item: [Edge; 2]) {
        self.0.push(item);
    }
}
