import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (x₀ : Int),
  (0 ≤ x₀) ->
   (0 ≤ (x₀ + 1))
end F
