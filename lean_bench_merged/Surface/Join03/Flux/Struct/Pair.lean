import Surface.Join03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Pair  where
  mkPair₀ ::
    a : Int 
    b : Int 
  deriving Inhabited
attribute [grind .] Pair.ext


end F
