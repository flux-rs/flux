import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.ROOTNANOSPERSEC
import LeanFixpoint
open Classical

namespace F



def Test32 := 
 ∀ (nanos₀ : Int),
  (nanos₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (((nanos₀ % 1000000000) ≤ 4294967295) -> (a'₁ = (nanos₀ % 1000000000))) ->
      ((0 ≤ a'₁)) ∧
      ((a'₁ < ROOT_NANOS_PER_SEC))
      
end F
