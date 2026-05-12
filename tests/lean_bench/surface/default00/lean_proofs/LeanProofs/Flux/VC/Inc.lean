import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Inc := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   (¬(x₀ < y₀)) ->
    (x₀ < (x₀ + 1))
end F
