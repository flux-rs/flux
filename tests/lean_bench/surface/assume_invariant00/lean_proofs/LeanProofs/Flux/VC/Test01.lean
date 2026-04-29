import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := 
 ∀ (len₀ : Int),
  (len₀ > 0) ->
   (len₀ ≥ 0) ->
    (len₀ ≤ 18446744073709551615) ->
     (0 < len₀)
end F
