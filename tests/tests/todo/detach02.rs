struct MyStruct {
    x: i32,
}

impl MyStruct {
    fn foo(&self) -> i32 {
        12
    }
}

// #[flux::specs {

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
// const test3: () = {};
