// TODO: flux-core/ssrc/iter/adapters/zip.rs

// use flux_attrs::*;

// #[extern_spec(core::iter)]
// #[refined_by(a: A, b: B)]
// struct Zip<A, B>;

// defs! {
//     fn min(x: int, y: int) -> int {
//         if x < y { x } else { y }
//     }
// }

// #[extern_spec(core::iter)]
// #[assoc(
//     fn size(r: Zip<A, B>) -> int {
//       min(<A as Iterator>::size(r.a), <B as Iterator>::size(r.b))
//     }

//     fn done(r: Zip<A, B>) -> bool {
//       <A as Iterator>::done(r.a) || <B as Iterator>::done(r.b)
//     }

//     fn step(self: Zip<A, B>, other: Zip<A, B>) -> bool {
//       <A as Iterator>::step(self.a, other.a) && <B as Iterator>::step(self.b, other.b)
//     }
// )]
// impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
//     #[spec(
//         fn(self: &mut Self[@curr_s]) -> Option<_>[!<Self as Iterator>::done(curr_s)]
//         ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)}
//     )]
//     fn next(&mut self) -> Option<<Zip<A, B> as Iterator>::Item>;
// }

// #[extern_spec(core::iter)]
// #[spec(fn(a: A, b: B) -> Zip<A::IntoIter, B::IntoIter>[a, b])]
// fn zip<A, B>(a: A, b: B) -> Zip<A::IntoIter, B::IntoIter>
// where
//     A: IntoIterator,
//     B: IntoIterator;
