import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def AddColorcode := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (c₀ : Int),
  (∀ (a'₀ : Int),
   ((k0 a'₀ c₀)) ->
    (a'₀ ≥ 0) ->
     ((c₀ = 1) ->
      ((k1 (a'₀ + 1) a'₀ c₀))) ∧
     ((c₀ = 2) ->
      ((k1 (a'₀ + 2) a'₀ c₀))) ∧
     ((c₀ = 3) ->
      ((k1 (a'₀ + 3) a'₀ c₀)))
     ) ∧
  (∀ (a'₁ : Int),
   ((k2 a'₁ c₀)) ->
    (((k0 a'₁ c₀))) ∧
    (∀ (a'₂ : Int),
     ((k1 a'₂ a'₁ c₀)) ->
      ((k3 a'₂ c₀)))
    ) ∧
  (∀ (a'₃ : Int),
   ((k2 a'₃ c₀))) ∧
  (∀ (a'₄ : Int),
   ((k3 a'₄ c₀)) ->
    (a'₄ ≥ c₀))
  
end F
