use flux_rs::attrs::*;

defs! {
    local qualifier MyQ1(x: int, y: int, z: int) { x + y == z }

    // local qualifier MyQ2<T1, T2, T3>(x: T1, y: T2, z: T3) { x + y == z }
}

// #[qualifiers(MyQ1)]
// #[spec(fn (n: usize) -> usize[n])]
// pub fn test_with_qualifier(n: usize) -> usize {
//     let mut i = n;
//     let mut res = 0;
//     while i > 0 {
//         i -= 1;
//         res += 1;
//     }
//     res
// }

#[spec(fn (n: usize) -> usize[n])]
pub fn test_with_qualifier(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        #[flux::defs{
            invariant qualifier Auto(x:int, y:int, z: int) { x + y == z }
            // invariant qualifier Auto() { x + y == z }
        }]
        const _: () = ();
        i -= 1;
        res += 1;
    }
    res
}

// #[spec(fn (n: usize) -> usize[n])]
// pub fn test(n: usize) -> usize {
//     let mut i = n;
//     let mut res = 0;
//     while i > 0 {
//         invariant!(res + i == n);
//         i -= 1;
//         res += 1;
//     }
//     res
// }
