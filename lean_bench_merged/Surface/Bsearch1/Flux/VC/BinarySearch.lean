import Surface.Bsearch1.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BinarySearch := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   (n₀ ≥ 0) ->
    (0 ≤ n₀) ->
     (n₀ ≥ 0) ->
      ((¬(n₀ ≤ 0)) ->
       (((n₀ - 1) ≥ 0)) ∧
       (((k0 0 (n₀ - 1) n₀ k₀))) ∧
       (∀ (low₀ : Int),
        ∀ (high₀ : Int),
         ((k0 low₀ high₀ n₀ k₀)) ->
          ((¬(low₀ ≤ high₀)) ->
           (n₀ ≤ n₀)) ∧
          ((low₀ ≤ high₀) ->
           (((high₀ - low₀) ≥ 0)) ∧
           ((((low₀ + ((high₀ - low₀) / 2)) < n₀)) ∧
           (∀ (a'₃ : Int),
            ((k1 a'₃ n₀ k₀ low₀ high₀))) ∧
           (∀ (a'₄ : Int),
            ((k1 a'₄ n₀ k₀ low₀ high₀)) ->
             ((a'₄ ≠ k₀) ->
              ((¬(a'₄ > k₀)) ->
               ((k2 high₀ n₀ k₀ low₀ high₀ a'₄))) ∧
              ((a'₄ > k₀) ->
               (((low₀ + ((high₀ - low₀) / 2)) ≠ 0) ->
                ((((low₀ + ((high₀ - low₀) / 2)) - 1) ≥ 0)) ∧
                (((k2 ((low₀ + ((high₀ - low₀) / 2)) - 1) n₀ k₀ low₀ high₀ a'₄)))
                ) ∧
               ((¬((low₀ + ((high₀ - low₀) / 2)) ≠ 0)) ->
                ((k3 n₀ n₀ k₀ low₀ high₀ a'₄)))
               ) ∧
              (∀ (high₁ : Int),
               ((k2 high₁ n₀ k₀ low₀ high₀ a'₄)) ->
                ((¬(a'₄ < k₀)) ->
                 ((k4 low₀ n₀ k₀ low₀ high₀ a'₄ high₁))) ∧
                ((a'₄ < k₀) ->
                 ((k4 ((low₀ + ((high₀ - low₀) / 2)) + 1) n₀ k₀ low₀ high₀ a'₄ high₁))) ∧
                (∀ (low₁ : Int),
                 ((k4 low₁ n₀ k₀ low₀ high₀ a'₄ high₁)) ->
                  ((k0 low₁ high₁ n₀ k₀)))
                )
              ) ∧
             ((¬(a'₄ ≠ k₀)) ->
              ((k3 (low₀ + ((high₀ - low₀) / 2)) n₀ k₀ low₀ high₀ a'₄))) ∧
             (∀ (a'₇ : Int),
              ((k3 a'₇ n₀ k₀ low₀ high₀ a'₄)) ->
               ((k5 a'₇ n₀ k₀)))
             )
           )
           )
          )
       ) ∧
      ((n₀ ≤ 0) ->
       ((k5 n₀ n₀ k₀))) ∧
      (∀ (a'₈ : Int),
       ((k5 a'₈ n₀ k₀)) ->
        (a'₈ ≤ n₀))
      
end F
