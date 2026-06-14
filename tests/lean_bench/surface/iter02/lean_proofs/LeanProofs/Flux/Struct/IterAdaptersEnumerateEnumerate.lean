import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure IterAdaptersEnumerateEnumerate (t0 : Type) [Inhabited t0] where
  mkIterAdaptersEnumerateEnumerate₀ ::
    idx : Int 
    inner : t0 
  deriving Inhabited
attribute [grind .] IterAdaptersEnumerateEnumerate.ext


end F
