import Structs.Dot01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Pair  where
  mkPair₀ ::
    x : Int 
    y : Int 
  deriving Inhabited
attribute [grind .] Pair.ext


end F
