import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Blah3 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (∀ (v₀ : Int),
   (n₀ < v₀) ->
    ((k0 v₀ n₀))) ∧
  (∀ (a'₁ : Int),
   ((k0 a'₁ n₀)) ->
    (∀ (v₁ : Int),
     (a'₁ < v₁) ->
      ((k1 v₁ n₀ a'₁))) ∧
    (∀ (a'₃ : Int),
     ((k1 a'₃ n₀ a'₁)) ->
      (∀ (v₂ : Int),
       (a'₃ < v₂) ->
        ((k2 v₂ n₀ a'₁ a'₃))) ∧
      (∀ (a'₅ : Int),
       ((k2 a'₅ n₀ a'₁ a'₃)) ->
        (((k3 a'₅ n₀ a'₁ a'₃ a'₅))) ∧
        (∀ (a'₆ : Int),
         ((k3 a'₆ n₀ a'₁ a'₃ a'₅)) ->
          (n₀ < a'₆))
        )
      )
    )
  
end F
