import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Range
import LeanFixpoint
open Classical

namespace F



def Test := 
 ∀ (r₀ : Range),
  ((Range.a r₀) ≤ (Range.b r₀)) ->
   ((((Range.b r₀) - (Range.a r₀)) ≥ 0) = True)
end F
