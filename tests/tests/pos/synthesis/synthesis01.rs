flux_rs::defs! {
    opaque sort ISeq;
    fn singleton(v: int) -> ISeq;
    fn cons(v: int, elems: ISeq) -> ISeq;
    fn head(v: ISeq) -> int;
}

#[flux::opaque]
#[flux::refined_by(elems: ISeq)]
struct Foo {}

#[flux::trusted]
impl Foo {
    #[flux::sig(fn(i32[@v]) -> Foo[singleton(v)])]
    fn singleton(_v: i32) -> Foo { Self {} }

    #[flux::sig(fn(&Self[@elems], i32[@v]) -> Foo[cons(v, elems)])]
    fn push(&self, _v: i32) -> Foo { Self {} }

    #[flux::sig(fn(&Self[@elems]) -> i32[head(elems)])]
    fn head(&self) -> i32 { 0 }
}

#[flux::sig(fn() -> Foo[singleton(1)])]
fn test00() -> Foo {
    Foo::singleton(1)
}

#[flux::sig(fn() -> Foo[cons(2, singleton(1))])]
fn test01() -> Foo {
    Foo::singleton(1).push(2)
}

#[flux::should_fail]
#[flux::sig(fn() -> i32[2])]
fn test02() -> i32 {
    let foo1 = Foo::singleton(1);
    let foo2 = foo1.push(2);
    foo2.head()
}

#[flux::trusted]
#[flux::sig(fn(i32[@v], &Foo[@elems]) ensures head(cons(v, elems)) == v)]
fn head_cons_eq(_v: i32, _foo: &Foo) {}

#[flux::sig(fn() -> i32[2])]
fn test03() -> i32 {
    let foo1 = Foo::singleton(1);
    let foo2 = foo1.push(2);
    head_cons_eq(2, &foo1); // Lemma instantiation
    foo2.head()
}