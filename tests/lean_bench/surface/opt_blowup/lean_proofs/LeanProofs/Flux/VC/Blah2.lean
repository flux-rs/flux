import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Blah2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
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
      (((k2 a'₃ n₀ a'₁ a'₃))) ∧
      (∀ (a'₄ : Int),
       ((k2 a'₄ n₀ a'₁ a'₃)) ->
        (n₀ < a'₄))
      )
    )
  
end F
