import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I64U32Lossless := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 42)) ->
    (a'₀ = 42)
end F
