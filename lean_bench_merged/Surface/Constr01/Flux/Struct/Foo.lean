import Surface.Constr01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Foo  where
  mkFoo₀ ::
    a : Int 
    b : Int 
  deriving Inhabited
attribute [grind .] Foo.ext


end F
