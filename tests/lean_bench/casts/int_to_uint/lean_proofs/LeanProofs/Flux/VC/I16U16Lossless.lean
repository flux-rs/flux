import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I16U16Lossless := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 1)) ->
    (a'₀ = 1)
end F
