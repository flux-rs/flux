import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__1__Pop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀))) ∧
   (((n₀ = 0) ->
    ((k1 False 0 n₀))) ∧
   (∀ (n₁ : Int),
    (n₀ = (n₁ + 1)) ->
     (n₁ ≥ 0) ->
      ∀ (a'₂ : Int),
       ((k0 a'₂ n₀)) ->
        ((k1 True n₁ n₀))) ∧
   (∀ (a'₃ : Prop),
    ∀ (a'₄ : Int),
     ((k1 a'₃ a'₄ n₀)) ->
      ((a'₄ ≥ 0)) ∧
      ((a'₃ = (n₀ > 0))) ∧
      ((a'₄ = (if (n₀ > 0) then (n₀ - 1) else n₀)))
      )
   )
   
end F
