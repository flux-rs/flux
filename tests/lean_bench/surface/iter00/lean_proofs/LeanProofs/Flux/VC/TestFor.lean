import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestFor := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k0 a'₁) ->
    ∀ (a'₂ : Int),
     ((110 ≤ a'₂) ∧ (a'₂ < 115)) ->
      (((k1 True a'₂))) ∧
      (∀ (a'₃ : Prop),
       ((k1 a'₃ a'₂)) ->
        (a'₃ = True))
      )
 
end F
