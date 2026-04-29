import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#3}MAX
import LeanFixpoint
open Classical

namespace F



def TestUpperBoundedUsErr := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (True -> (a'₁ = 9223372036854775807)) ->
      (x₀ > a'₁) ->
       ((¬(x₀ ≤ num_{impl#3}_MAX)) = True)
end F
