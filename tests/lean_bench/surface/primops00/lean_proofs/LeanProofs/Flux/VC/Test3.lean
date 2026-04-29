import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test3 := 
 ∀ (byte₀ : Int),
  (byte₀ ≤ 127) ->
   (byte₀ ≥ 0) ->
    ((16 * (c0 byte₀ 4)) = byte₀) ->
     ((c1 byte₀ 15) ≤ 15) ->
      ((((c0 byte₀ 4) ≤ 15) = True)) ∧
      ((((c1 byte₀ 15) ≤ 15) = True))
      
end F
