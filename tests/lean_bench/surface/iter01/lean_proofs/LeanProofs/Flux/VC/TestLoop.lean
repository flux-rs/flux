import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (vec₀ : Int),
  (0 ≤ vec₀) ->
   (∀ (v₀ : Int),
    (0 ≤ v₀) ->
     ((k0 v₀ vec₀))) ∧
   (((k1 vec₀))) ∧
   (∀ (a'₂ : Int),
    ((k0 a'₂ vec₀)) ->
     ((k2 a'₂ vec₀))) ∧
   (((k1 vec₀)) ->
    (∀ (a'₃ : Int),
     ((k2 a'₃ vec₀)) ->
      ((k3 a'₃ vec₀))) ∧
    (∀ (a'₄ : Int),
     ((k3 a'₄ vec₀)) ->
      (((0 ≤ a'₄) = True)) ∧
      (∀ (a'₅ : Int),
       ((k3 a'₅ vec₀)) ->
        ((k2 a'₅ vec₀)))
      )
    )
   
end F
