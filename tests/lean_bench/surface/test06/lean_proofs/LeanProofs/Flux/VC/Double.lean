import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Double := 
 ∀ (x₀ : Int),
  (0 < x₀) ->
   (x₀ < (x₀ + x₀))
end F
