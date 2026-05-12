import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test00F := 
 ∀ (b₀ : Int),
  ∀ (a₀ : Int),
   (b₀ > a₀) ->
    ((b₀ - a₀) > 0)
end F
