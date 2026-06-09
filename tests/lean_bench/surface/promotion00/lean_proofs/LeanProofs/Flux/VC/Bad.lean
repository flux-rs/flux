import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bad := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (((k1 0))) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k2 a'₁)) ∧
 (((k3 0))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k2 a'₂) ->
    ∀ (a'₃ : Int),
     ((k3 a'₃)) ->
      ∀ (a'₄ : Int),
       (a'₄ = 0) ->
        (k0 a'₄) ->
         ∀ (a'₅ : Int),
          ((k1 a'₅)) ->
           ((a'₃ = a'₅) = True))
 
end F
