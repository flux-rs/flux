// Annotations are checked against the Rust signature modulo normalization of projections.

use flux_attrs::*;

pub trait Trait {
    type Item;
}

impl Trait for () {
    type Item = u8;
}

impl Trait for bool {
    type Item = u8;
}

impl<T> Trait for Vec<T> {
    type Item = T;
}

pub trait Other {
    type Out;
}

impl Other for () {
    type Out = u8;
}

// Projection in the annotation, concrete type in Rust.
#[spec(fn() -> <() as Trait>::Item)]
pub fn get() -> u8 {
    0
}

// Concrete type in the annotation, projection in Rust.
#[spec(fn() -> u8{v: v > 0})]
pub fn get_pos() -> <() as Trait>::Item {
    1
}

// The refinement on the concrete type is used when checking the caller.
#[spec(fn() -> u8{v: v > 0})]
pub fn test() -> u8 {
    get_pos()
}

// Different projections that normalize to the same type.
#[spec(fn() -> <() as Trait>::Item)]
pub fn alias_alias() -> <bool as Trait>::Item {
    0
}

// Projections of different associated items that normalize to the same type.
#[spec(fn() -> <() as Other>::Out)]
pub fn alias_alias_other() -> <() as Trait>::Item {
    0
}

// Projection with generic arguments.
#[spec(fn(x: T) -> <Vec<T> as Trait>::Item)]
pub fn id<T>(x: T) -> T {
    x
}

// Projection resolved through a where-clause.
#[spec(fn(x: u8) -> T::Item)]
pub fn from_bound<T: Trait<Item = u8>>(x: u8) -> u8 {
    x
}

// Projection inside a type constructor.
#[spec(fn(x: Option<<() as Trait>::Item>) -> Option<u8>)]
pub fn option(x: Option<u8>) -> Option<<() as Trait>::Item> {
    x
}

// Projection in a struct field.
#[refined_by()]
pub struct S {
    #[field(<() as Trait>::Item)]
    pub f: u8,
}

// Match projection arguments before normalizing away the Rust projection.
#[spec(fn() -> <Vec<_> as Trait>::Item)]
pub fn type_hole() -> <Vec<u8> as Trait>::Item {
    0
}

impl<T> Trait for &T {
    type Item = u8;
}

// Elided lifetimes are holes too.
#[spec(fn() -> <&u8 as Trait>::Item)]
pub fn lifetime_hole() -> <&'static u8 as Trait>::Item {
    0
}

// Each component must match before normalization, even when another component needs it.
#[spec(fn(x: Option<<Vec<_> as Trait>::Item>) -> <() as Other>::Out)]
pub fn nested_hole(x: Option<<Vec<u8> as Trait>::Item>) -> <() as Trait>::Item {
    x.unwrap_or(0)
}

pub trait Family<T> {
    type Out;
}

impl<T> Family<T> for (u8, ())
where
    (u16, bool): Family<T>,
{
    type Out = <(u16, bool) as Family<T>>::Out;
}

// The first attempt fills `_` with u8 before failing on bool vs (). After normalization,
// the retry must overwrite that assignment with u16.
#[spec(fn(x: _) -> <(_, bool) as Family<T>>::Out)]
pub fn retry_hole<T>(x: <(u8, ()) as Family<T>>::Out) -> <(u8, ()) as Family<T>>::Out
where
    (u16, bool): Family<T>,
{
    x
}

// Projection in a type alias.
#[flux::alias(type Pos[v: int] = {<() as Trait>::Item[v] | v > 0})]
pub type Pos = u8;

#[spec(fn() -> Pos)]
pub fn pos() -> u8 {
    1
}

// Projection in a function pointer.
#[spec(fn(f: fn(<() as Trait>::Item) -> u8) -> u8)]
pub fn call(f: fn(u8) -> <() as Trait>::Item) -> u8 {
    f(0)
}
