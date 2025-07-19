#![flux::specs {

    enum List<T>
        refined_by(len: int)
        invariant(len >= 0)
    {
      Cons(T, List<T>[@n]) -> List<T>[n+1],
      Nil                  -> List<T>[0],
    }

}]

// #![flux::specs {
//     mod core {
//         mod option {
//             #[refined_by(valid: bool)]
//             enum Option<T> {
//               #[variant((T) -> Option<T>[{valid: true}])]
//               Some(T),
//               #[variant(Option<T>[{valid: false}])]
//               None,
//             }

//             impl Option<T> {
//                 fn is_some(&Self[@valid]) -> bool[valid];
//             }
//         }
//     }
// }]

struct MyStruct {
    x: usize,
    y: usize,
}

#[refined_by(vx: int, vy: int)]
struct MyStructOrig {
    #[field(usize[vx])]
    x: usize,
    #[field({usize[vy] | vx < vy})]
    y: usize,
}

impl MyStruct {
    fn foo(&self) -> i32 {
        12
    }
}
