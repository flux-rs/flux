import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmpSearch := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ((0 < m₀) ∧ (m₀ ≤ n₀)) ->
    (0 ≤ m₀) ->
     (0 ≤ n₀) ->
      ((m₀ > 0)) ∧
      ((((k0 0 0 0 m₀ n₀))) ∧
      (∀ (t_i₀ : Int),
       ∀ (p_i₀ : Int),
        ∀ (result_idx₀ : Int),
         ((k0 t_i₀ p_i₀ result_idx₀ m₀ n₀)) ->
          (n₀ ≥ 0) ->
           (t_i₀ < n₀) ->
            (m₀ ≥ 0) ->
             (p_i₀ < m₀) ->
              (∀ (a'₃ : Int),
               ((k1 a'₃ m₀ n₀ t_i₀ p_i₀ result_idx₀))) ∧
              (∀ (a'₄ : Int),
               ((k1 a'₄ m₀ n₀ t_i₀ p_i₀ result_idx₀)) ->
                (a'₄ ≥ 0) ->
                 (∀ (a'₅ : Int),
                  ((k2 a'₅ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄))) ∧
                 (∀ (a'₆ : Int),
                  ((k2 a'₆ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄)) ->
                   (a'₆ ≥ 0) ->
                    ((a'₄ ≠ a'₆) ->
                     ((p_i₀ ≠ 0) ->
                      (((p_i₀ - 1) ≥ 0)) ∧
                      (((p_i₀ - 1) < m₀)) ∧
                      (∀ (v₀ : Int),
                       (v₀ < m₀) ->
                        ((k3 v₀ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆))) ∧
                      (∀ (a'₈ : Int),
                       ((k3 a'₈ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)) ->
                        (a'₈ ≥ 0) ->
                         ((k4 a'₈ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)))
                      ) ∧
                     ((¬(p_i₀ ≠ 0)) ->
                      ((k4 0 m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆))) ∧
                     (∀ (p_i₁ : Int),
                      ((k4 p_i₁ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)) ->
                       ((k5 p_i₁ 0 m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)))
                     ) ∧
                    ((¬(a'₄ ≠ a'₆)) ->
                     ((result_idx₀ ≠ 0) ->
                      ((k6 result_idx₀ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆))) ∧
                     ((¬(result_idx₀ ≠ 0)) ->
                      ((k6 t_i₀ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆))) ∧
                     (∀ (result_idx₁ : Int),
                      ((k6 result_idx₁ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)) ->
                       (¬((p_i₀ + 1) ≥ m₀)) ->
                        ((k5 (p_i₀ + 1) result_idx₁ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)))
                     ) ∧
                    (∀ (p_i₂ : Int),
                     ∀ (result_idx₂ : Int),
                      ((k5 p_i₂ result_idx₂ m₀ n₀ t_i₀ p_i₀ result_idx₀ a'₄ a'₆)) ->
                       ((k0 (t_i₀ + 1) p_i₂ result_idx₂ m₀ n₀)))
                    )
                 )
              )
      )
      
end F
