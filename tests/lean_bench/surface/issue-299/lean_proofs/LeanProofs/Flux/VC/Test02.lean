import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.S2
import LeanFixpoint
open Classical

namespace F



def Test02 := 
 ∀ (x₀ : Int),
  ∀ (a'₁ : S2),
   ∀ (v₀ : Int),
    (v₀ > 0) ->
     ∀ (a'₃ : Int),
      ((S2.b a'₁) > 0) ->
       ∀ (v₁ : Int),
        (v₁ > 0) ->
         (((v₁ + 1) > 0)) ∧
         (((v₀ + 1) > 0))
         
end F
