import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Sub := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (b₀ ≤ a₀) ->
    ((0 ≤ (a₀ - b₀)) = True)
end F
