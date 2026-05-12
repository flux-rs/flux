import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def DivUnsigned := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (b₀ > 0) ->
    (a₀ ≥ 0) ->
     (b₀ ≥ 0) ->
      (b₀ ≠ 0)
end F
