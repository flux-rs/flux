import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k1 a'₀)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   ((k2 a'₁))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k1 a'₂) ->
    ∀ (a'₃ : Int),
     ((k2 a'₃)) ->
      (a'₃ > 0))
 
end F
