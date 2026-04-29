import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestIndexAfterIsEmpty := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ ≠ 0) ->
    (0 < a'₀)
end F
