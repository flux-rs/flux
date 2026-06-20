import Surface.Issue299.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure S2  where
  mkS2₀ ::
    a : Int 
    b : Int 
  deriving Inhabited
attribute [grind .] S2.ext


end F
