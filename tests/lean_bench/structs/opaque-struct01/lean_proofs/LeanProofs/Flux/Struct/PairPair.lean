import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PairPair  where
  mkPairPair₀ ::
    a : Int 
    b : Int 
  deriving Inhabited
attribute [grind .] PairPair.ext


end F
