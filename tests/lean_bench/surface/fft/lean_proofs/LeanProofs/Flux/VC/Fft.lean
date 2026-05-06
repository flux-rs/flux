import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Fft := 
 ∀ (n₀ : Int),
  (2 ≤ n₀) ->
   (0 ≤ n₀) ->
    ((n₀ > 0)) ∧
    (∀ (a'₀ : Int),
     (n₀ > 0))
    
end F
