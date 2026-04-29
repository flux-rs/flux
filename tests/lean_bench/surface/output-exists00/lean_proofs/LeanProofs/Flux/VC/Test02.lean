import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test02 := 
 ∀ (n₀ : Int),
  ∀ (v₀ : Int),
   (v₀ > n₀) ->
    ((v₀ - n₀) > 0)
end F
