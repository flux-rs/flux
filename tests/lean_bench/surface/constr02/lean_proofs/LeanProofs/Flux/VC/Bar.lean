import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Bar := 
 ∀ (a₀ : Int),
  ∀ (a'₀ : Int),
   ((0 < a₀) ∧ (a'₀ = a₀)) ->
    (0 < a'₀)
end F
