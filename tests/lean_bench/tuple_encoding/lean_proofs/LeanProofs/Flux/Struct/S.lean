import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure S  where
  mkS₀ ::
    x : Int 
    y : Int 
  deriving Inhabited
attribute [grind .] S.ext


end F
