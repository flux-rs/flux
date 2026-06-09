import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def CloseOnMove := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k0 a'₁) ->
    ∀ (v₀ : Int),
     (v₀ > 0) ->
      ((v₀ + 1) > 0))
 
end F
