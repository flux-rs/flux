import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure IterAdaptersEnumerateEnumerate (t0 : Type) [Inhabited t0] where
  mkIterAdaptersEnumerateEnumerate₀ ::
    idx : Int
    inner : t0

instance [Inhabited t0] : Inhabited (IterAdaptersEnumerateEnumerate t0) where
  default := ⟨default, default⟩
end F
