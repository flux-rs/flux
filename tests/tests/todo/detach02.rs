#![flux::specs {

    enum Option<T>[valid: bool]
    {
      Some(T) -> Option<T>[true],
      None    -> Option<T>[false],
    }

    enum List<T>[len: int]
      invariant(len >= 0)
    {
      Cons {x: T, y: List<T>[@n]} -> List<T>[n+1],
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
