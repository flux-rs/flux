import Structs.OpaqueRange.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Range  where
  mkRange₀ ::
    a : Int 
    b : Int 
  deriving Inhabited
attribute [grind .] Range.ext


end F
