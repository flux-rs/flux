import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BobTest2 := 
 ∀ (v₀ : Int),
  (v₀ ≥ 0) ->
   (v₀ < 10) ->
    ∀ (v₁ : Int),
     (v₁ ≥ 0) ->
      (v₁ < 10) ->
       ∀ (v₂ : Int),
        (v₂ ≥ 0) ->
         (v₂ < 10) ->
          (((v₀ + v₁) + v₂) < 30)
end F
