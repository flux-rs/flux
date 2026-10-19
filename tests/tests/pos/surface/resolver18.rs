//! `self` inside a nested `use` tree binds the name of the enclosing module, e.g.,
//! `use crate::a::{self}` brings `a` into scope, not `self`.
#![allow(dead_code, unused_imports)]

mod outer {
    pub mod mpu {
        #[flux::refined_by(n: int)]
        pub struct Region {
            #[flux::field(i32[n])]
            pub val: i32,
        }
    }

    pub mod syscall {
        #[flux::refined_by(b: bool)]
        pub struct Syscall {
            #[flux::field(bool[b])]
            pub flag: bool,
        }
    }
}

mod self_alone {
    // Two `{self}` imports in the same module must not clash as duplicate definitions of `self`.
    use crate::outer::mpu::{self};
    use crate::outer::syscall::{self, Syscall};

    #[flux::sig(fn(x: mpu::Region[1]) -> i32[1])]
    fn test00(x: mpu::Region) -> i32 {
        x.val
    }

    #[flux::sig(fn(x: syscall::Syscall[true], y: Syscall[true]) -> bool[true])]
    fn test01(x: syscall::Syscall, y: Syscall) -> bool {
        x.flag && y.flag
    }
}

mod self_renamed {
    use crate::outer::{mpu::{self as m}};

    #[flux::sig(fn(x: m::Region[1]) -> i32[1])]
    fn test(x: m::Region) -> i32 {
        x.val
    }
}
