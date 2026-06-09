import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Range
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ∀ (r₀ : Range),
  ((Range.a r₀) ≤ (Range.b r₀)) ->
   ((((Range.b r₀) - (Range.a r₀)) ≥ 0) = True)
end F
