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

## Dot-Syntax
