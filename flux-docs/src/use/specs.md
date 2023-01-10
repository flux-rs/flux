# Flux Specification Guide

This is a WIP guide to writing specifications in `flux`.

## Grammar of Refinements

Note: This changes frequently! For most up-to-date grammar see [`surface_grammar.lalrpop`](flux-syntax/src/surface_grammar.lalrpop)

```
e ::= n                     // numbers 1,2,3...
    | x                     // identifiers x,y,z...
    | x.f                   // index-field access
    | e + e                 // addition
    | e - e                 // subtraction
    | n * e                 // multiplication by constant
    | if p { e } else { e } // if-then-else
    | f(e...)               // uninterpreted function application

p ::= true | false
    | e = e   // equality
    | e < e   // less than
    | p || p  // disjunction
    | p && p  // conjunction
    | p => p  // implication
    | !p      // negation
```
