import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I64Max := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 9223372036854775807)) ->
    (a'₀ = 9223372036854775807)
end F
