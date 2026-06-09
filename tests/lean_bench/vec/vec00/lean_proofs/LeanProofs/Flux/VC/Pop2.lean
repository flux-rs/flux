import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Pop2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ > 2) ->
   (0 ≤ n₀) ->
    (∀ (a'₀ : Int),
     ((k0 a'₀ n₀))) ∧
    ((0 ≤ (if (n₀ > 0) then (n₀ - 1) else 0)) ->
     (∀ (a'₁ : Int),
      ((k0 a'₁ n₀)) ->
       ((k1 a'₁ n₀))) ∧
     (((n₀ > 0) = True)) ∧
     (∀ (v1₀ : Int),
      ((k1 v1₀ n₀)) ->
       (∀ (a'₃ : Int),
        ((k0 a'₃ n₀)) ->
         ((k2 a'₃ n₀ v1₀))) ∧
       ((0 ≤ (if ((if (n₀ > 0) then (n₀ - 1) else 0) > 0) then ((if (n₀ > 0) then (n₀ - 1) else 0) - 1) else 0)) ->
        (∀ (a'₄ : Int),
         ((k2 a'₄ n₀ v1₀)) ->
          ((k3 a'₄ n₀ v1₀))) ∧
        ((((if (n₀ > 0) then (n₀ - 1) else 0) > 0) = True)) ∧
        (∀ (v2₀ : Int),
         ((k3 v2₀ n₀ v1₀)) ->
          ((if ((if (n₀ > 0) then (n₀ - 1) else 0) > 0) then ((if (n₀ > 0) then (n₀ - 1) else 0) - 1) else 0) = (n₀ - 2)))
        )
       )
     )
    
end F
