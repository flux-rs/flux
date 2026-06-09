import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.S2
open Classical
set_option linter.unusedVariables false


namespace F



def Test04 := 
 ∀ (x₀ : Int),
  (x₀ = 10) ->
   ∀ (a'₁ : S2),
    ∀ (a'₂ : Int),
     ((S2.b a'₁) > 0) ->
      ∀ (v₀ : Int),
       (v₀ > 0) ->
        ((v₀ + 1) > 0)
end F
