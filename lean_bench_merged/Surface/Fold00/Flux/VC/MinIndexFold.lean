import Surface.Fold00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MinIndexFold := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (k₀ : Int),
  (0 < k₀) ->
   (0 ≤ k₀) ->
    (k₀ ≥ 0) ->
     (0 ≤ (k₀ - 0)) ->
      (∀ (a'₀ : Int),
       ∀ (a'₁ : Int),
        ((k0 a'₀ a'₁ k₀)) ->
         (a'₀ ≥ 0) ->
          (a'₁ ≥ 0) ->
           ((a'₁ < k₀)) ∧
           ((a'₀ < k₀)) ∧
           (∀ (a'₂ : Prop),
            ((¬a'₂) ->
             ((k1 a'₀ a'₀ a'₁ k₀))) ∧
            (a'₂ ->
             ((k1 a'₁ a'₀ a'₁ k₀)))
            )
           ) ∧
      (∀ (a'₃ : Int),
       ((k2 a'₃ k₀)) ->
        ∀ (a'₄ : Int),
         ((k3 a'₄ k₀)) ->
          (((k0 a'₃ a'₄ k₀))) ∧
          (∀ (a'₅ : Int),
           ((k1 a'₅ a'₃ a'₄ k₀)) ->
            ((k2 a'₅ k₀)))
          ) ∧
      (∀ (v₀ : Int),
       ((0 ≤ v₀) ∧ (v₀ < k₀)) ->
        ((k3 v₀ k₀))) ∧
      (((k2 0 k₀))) ∧
      (∀ (a'₇ : Int),
       ((k2 a'₇ k₀)) ->
        (a'₇ ≥ 0) ->
         (a'₇ < k₀))
      
end F
