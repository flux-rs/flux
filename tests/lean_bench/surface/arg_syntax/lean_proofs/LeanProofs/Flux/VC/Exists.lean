import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Exists := 
 ∀ (v₀ : Int),
  ((v₀ > 0) ∧ (v₀ < 10)) ->
   (((v₀ + 1) > 0)) ∧
   (((v₀ + 1) < 11))
   
end F
