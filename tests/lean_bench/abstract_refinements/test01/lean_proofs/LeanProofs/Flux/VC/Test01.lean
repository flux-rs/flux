import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (a₀ < b₀) ->
    ((b₀ - a₀) > 0)
end F
