import Surface.Box02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MoveOutOfBox := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (((k1 0))) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k2 a'₁)) ∧
 (∀ (a'₂ : Int),
  ((k1 a'₂)) ->
   ((k3 a'₂))) ∧
 (∀ (a'₃ : Int),
  (a'₃ = 0) ->
   (k2 a'₃) ->
    ∀ (a'₄ : Int),
     ((k3 a'₄)) ->
      (a'₄ ≥ 0))
 
end F
