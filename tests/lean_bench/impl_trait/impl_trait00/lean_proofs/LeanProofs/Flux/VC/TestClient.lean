import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestClient := 
 ∀ (it₀ : Int),
  ∀ (a'₁ : Int),
   ∀ (a'₂ : Int),
    (1 ≤ a'₂) ->
     (0 ≤ a'₂)
end F
