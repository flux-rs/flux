import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def ConstToU8 := 
 (97 ≤ 1114111) ->
  (0 ≤ 97) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     ((97 ≤ 255) -> (a'₀ = 97)) ->
      (a'₀ = 97)
end F
