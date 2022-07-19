#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub fn test(val: i32) {
    if 10 < val {
        assert(100 < val) //~ ERROR precondition
    }
}
mod foo {
    #![flux::ignore] // ignore checking this module (and all its contents)

    mod goo {

        mod coo {
            #[flux::sig(fn(Vec<i32{v:0 < v}>) -> ())]
            pub fn test_map(vec: Vec<i32>) {
                let _ = vec.into_iter().map(|val| assert!(10 < val));
            }
        }
    }

    pub fn test_crap(vec: Vec<i32>) {
        let _ = vec.into_iter().map(|val| assert!(10 < val));
    }
}
