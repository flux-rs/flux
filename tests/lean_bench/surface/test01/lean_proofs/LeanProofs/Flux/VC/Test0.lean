import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test0 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (m₀ : Int),
   ∀ (b₀ : Prop),
    (n₀ < m₀) ->
     ((¬b₀) ->
      (((k0 m₀ n₀ m₀ b₀))) ∧
      (((k1 n₀ m₀ b₀))) ∧
      (((k2 n₀ n₀ m₀ b₀))) ∧
      (∀ (a'₁ : Int),
       ((k0 a'₁ n₀ m₀ b₀)) ->
        ((k3 a'₁ n₀ m₀ b₀))) ∧
      (∀ (a'₂ : Int),
       ((k0 a'₂ n₀ m₀ b₀)) ->
        ((k4 a'₂ n₀ m₀ b₀))) ∧
      (∀ (a'₃ : Int),
       ((k4 a'₃ n₀ m₀ b₀)) ->
        ((k0 a'₃ n₀ m₀ b₀)))
      ) ∧
     (b₀ ->
      (((k5 n₀ n₀ m₀ True))) ∧
      (((k1 n₀ m₀ True))) ∧
      (∀ (a'₄ : Int),
       ((k5 a'₄ n₀ m₀ True)) ->
        ((k2 a'₄ n₀ m₀ True))) ∧
      (((k3 m₀ n₀ m₀ True))) ∧
      (∀ (a'₅ : Int),
       ((k5 a'₅ n₀ m₀ True)) ->
        ((k4 a'₅ n₀ m₀ True))) ∧
      (∀ (a'₆ : Int),
       ((k4 a'₆ n₀ m₀ True)) ->
        ((k5 a'₆ n₀ m₀ True)))
      ) ∧
     (((k1 n₀ m₀ b₀)) ->
      ∀ (a'₇ : Int),
       ((k4 a'₇ n₀ m₀ b₀)) ->
        (((k4 (a'₇ + 1) n₀ m₀ b₀))) ∧
        (∀ (a'₈ : Int),
         ((k4 a'₈ n₀ m₀ b₀)) ->
          ∀ (a'₉ : Int),
           ((k2 a'₉ n₀ m₀ b₀)) ->
            ∀ (a'₁₀ : Int),
             ((k3 a'₁₀ n₀ m₀ b₀)) ->
              (0 ≤ (a'₈ - n₀)))
        )
     
end F
