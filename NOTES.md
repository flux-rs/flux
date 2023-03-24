# RJ Notes

- [=] [Measures](https://hackmd.io/q7KU5P4dTXG4t0F60aIiOg)
- [ ] Projection? (Get `iter` working _without_ refinements... e.g. on plain `Vec`)
- [ ] Closure/FnPtr?

## UIF

- [x] tests

- [ ] surface
        - UFName, UFSort

- [ ] parse

- [ ] collect

## Measures

See [this](https://hackmd.io/q7KU5P4dTXG4t0F60aIiOg)

- [+] refactor to `PolyVariantDef`
- [+] `opt00.rs`
- [+] `list00.rs`

- [] manually write multiple measures
    - [] type `pred`
    - [] spec `is_var`
    - [] spec `is_nnf`

- [] merge "automatically" into single spec


```rust
spec size : int for List<T> {
    Nil -> 0
    Cons(T, Box<List<T>[@tl]) -> 1 + tl.size,
}

#[flux::refined_by(n:int)]
pub enum List<T> {
    #[flux::ctor(List<T>[0])]
    Nil,
    #[flux::ctor((T,Box<List<T>[@n]>) -> List<T>[n])]
    Cons(T, Box<List<T>>),
}



spec nnf : bool for Pred {
    Var : ( i32 )  -> true,
    Not : ( Box<Pred[@p1]> ) -> p1.is_var,
    And : ( Box<Pred[@p1]>, Box<Pred[@p2]>) -> p1.nnf && p2.nnf,
    Or  : ( Box<Pred[@p1]>, Box<Pred[@p2]>) -> p1.nnf && p2.nnf,
}
```



```rust
spec nnf : bool for Pred {
    Var : ( i32 )  -> true,
    Not : ( Box<Pred[@p1]> ) -> p1.is_var,
    And : ( Box<Pred[@p1]>, Box<Pred[@p2]>) -> p1.nnf && p2.nnf,
    Or  : ( Box<Pred[@p1]>, Box<Pred[@p2]>) -> p1.nnf && p2.nnf,
}
```


---

## TODO: Bitvectors

**Step 1**

What do constraints look like in SMTLIB?

- write constraints
- get them to pass

**Step 2**

What do constraints look like in `fixpoint`?

- add operators
- write constraints
- get them to pass

**Step 3**

- add sort: `bitvec32` or `bitvec64`

- add type `bv32` indexed by `bitvec32` sort

```rust
#[flux::refined_by(value: bitvec32)]
struct bv32 {
  inner: usize
}
```

- add rbitv: like `rvec.rs` but with and API using the updated fixpoint support

```rust
fn and(x:bv32, y:bv32) -> bv32
fn or(x:bv32, y:bv32) -> bv32
fn add(x:bv32, y:bv32) -> bv32
fn sub(x:bv32, y:bv32) -> bv32
fn to_bv32(n:usize) -> bv32[int2bv(n)]
fn to_usize(x:bv32) -> usize[bv2int(x)]
```

```rust
// Define pow2 as:
#[flux::defs(
    fn pow2(x:int)    -> bool { x < max_u32 => pow2bv(int2bv(x)) }; ???
    fn pow2bv(x:bv32) -> bool { (x & x - 1) == 0 } // hahaha -- apparently a well known trick!
  )]

#[flux::trusted] // bitvectors
#[flux::sig(fn (index: usize, size:Size) -> usize{v: v < size})]
fn wrap_index(index: usize, size: _Size) -> usize {
    // size is always a power of 2
    assert(is_power_of_two(size));
    index & (size - 1)
}

#[flux::sig(fn (index: usize, size:usize{pow2(size)}) -> usize{v: v < size})]
fn wrap_index(index: usize, size: usize) -> usize {
    assert(is_power_of_two(size));
    bv32::to_usize(bv32::and(bv32::usize_to_bv32(index), bv32::usize_to_bv32(bv32::sub(size, 1))))

    /*

    forall size, index.
        let size'  = int2bv(size)
            index' = int2bv(index)
        in
            let mask = bv_sub(size', int2bv(1))
            in
                let res = bv2int(bv_and(index', mask))
                in
                    pow2(size') => res < size
    */
}
```