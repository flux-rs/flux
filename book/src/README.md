<img src="img/logo-wide.svg" class="flux-logo" alt="Flux Logo">

<!-- Types bring order to code.

For example, if a variable `i:usize` then we know `i`
is a number that can be used to index a vector.
Similarly, if `v: Vec<&str>` then we can be sure that
`v` is a collection of strings which may _be_ indexed
but of course, not used _as_ an index.

However, by itself, `usize` doesn't tell us how big
or small the number and hence the programmer must
still rely on their own wits, a lot of tests, and
a dash of optimism, to ensure that all the different
bits snap together correctly at run-time. -->


Flux is a [**refinement type checker**][flux-github] plugin
for Rust that lets you *specify* a range of correctness properties
and have them be *verified* at compile time.

Flux works by extending Rust's types with [refinements][jhala-vazou]:
logical assertions describing additional correctness requirements
that are checked during compilation, thereby eliminating various
classes of run-time problems.

You can try it on the [**online playground**](https://flux.goto.ucsd.edu/).

Better still, read the [**interactive tutorial**](./01-refinements.md),
to learn how you can use Flux on your Rust code.

[jhala-vazou]: https://arxiv.org/abs/2010.07763
[flux-github]: https://github.com/flux-rs/flux/
