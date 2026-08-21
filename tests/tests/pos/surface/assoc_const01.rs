// Split into smaller staged tests in assoc_const02.rs .. assoc_const06.rs.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}

struct Thingy<T>(T);

impl<T> TraitWithConst for Thingy<T> {
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32 {
        if Self::IS_ZST { 0 } else { 100 }
    }
}

struct ThisIsOk;

impl TraitWithConst for ThisIsOk {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32[15])]
    fn silly_method() -> u32 {
        15
    }
}

//

struct Blingy<T>(T);

#[flux::trusted(reason = "extern-spec")]
#[flux::spec(fn() -> bool[T::size_of() == 0])]
fn fake_size_of<T>() -> bool {
    size_of::<T>() == 0
}

impl<T> TraitWithConst for Blingy<T> {
    #[flux::constant(T::size_of() == 0)]
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32 {
        let is_zst = fake_size_of::<T>();
        if is_zst { 0 } else { 100 }
    }
}
