import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test5 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ = x₀) -> ((c0 x₀ x₀) = 0)) ->
    ((c0 x₀ x₀) = 0)
end F
