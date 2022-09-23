# RJ Notes

- [=] [Measures](https://hackmd.io/q7KU5P4dTXG4t0F60aIiOg)
- [ ] Projection? (Get `iter` working _without_ refinements... e.g. on plain `Vec`)
- [ ] Closure/FnPtr?

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

## RJ edit

* A)
  ```rust=
  // SURFACE
  fn (p: Pair) -> i32[p.x + p.y]

  // DESUGAR
  forall a0: int, a1: int. fn(Pair<a0, a1>) -> i32<a0 + a1>
  ```

* C)
  ```rust=
  // SURFACE
  fn (p: Pair) -> i32[p.x]

  // DESUGAR
  forall a0: int, a1: int. fn(Pair<a0, a1>) -> i32<a0>
  ```

* D)
  ```rust=
  // SURFACE
  fn (a: i32, b: i32) -> Pair{v : v.x == a, v.y == b}

  // DESUGAR
  forall a: int, b: int. fn(i32<a>, i32<b>) -> Pair{v0 v1: v0 == a && v1 == b}
  // HARD forall a: int, b: int. fn(i32<a>, i32<b>) -> Pair<a, b>

  if you really want indices you can write

  // SURFACE
  fn (a: i32, b: i32) -> Pair[a,b]

  // DESUGAR
  forall a: int, b: int. fn(i32<a>, i32<b>) -> Pair<a, b>
  ```

* E)
  ```rust=
  // SURFACE
  fn (a: i32) -> Pair{v : v.x == a}

  // DESUGAR
  forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 == a}
  ```

* F)
  ```rust=
  // SURFACE
  fn (a: i32) -> Pair{v : v.x == a}

  // DESUGAR
  forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 == a}
  ```

* H)
  ```rust=
  // SURFACE
  fn (a: i32) -> Pair{v: v.x == a && v.y > 0}

  // DESUGAR
  forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 == a && v1 > 0}
  ```

* I)
  ```rust=
  // SURFACE
  fn (p: Pair{p.y > 0}) -> i32[p.x]

  // DESUGAR
  forall a0: int, a1: int. fn({Pair<a0, a1> : a1 > 0}) -> i32<a0>
  ```