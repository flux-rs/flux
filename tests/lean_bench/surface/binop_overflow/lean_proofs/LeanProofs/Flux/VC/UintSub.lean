import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def UintSub := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (b₀ < a₀) ->
    (a₀ ≥ 0) ->
     (a₀ ≤ 4294967295) ->
      (b₀ ≥ 0) ->
       (b₀ ≤ 4294967295) ->
        (((a₀ - b₀) ≥ 0)) ∧
        (((a₀ - b₀) ≤ 4294967295))
        
end F
