import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def KmpTable := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k11 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (len₀ : Int),
  (len₀ > 0) ->
   (0 ≤ len₀) ->
    (len₀ ≥ 0) ->
     (len₀ ≤ 18446744073709551615) ->
      (((k0 0 len₀))) ∧
      ((((k1 1 0 len₀))) ∧
      (∀ (a'₀ : Int),
       ((k0 a'₀ len₀)) ->
        ((k2 a'₀ 1 0 len₀))) ∧
      (∀ (i₀ : Int),
       ∀ (j₀ : Int),
        ((k1 i₀ j₀ len₀)) ->
         ((¬(i₀ < len₀)) ->
          ∀ (a'₃ : Int),
           ((k2 a'₃ i₀ j₀ len₀)) ->
            (a'₃ < len₀)) ∧
         ((i₀ < len₀) ->
          (∀ (a'₄ : Int),
           ((k3 a'₄ len₀ i₀ j₀))) ∧
          (∀ (a'₅ : Int),
           ((k3 a'₅ len₀ i₀ j₀)) ->
            (a'₅ ≥ 0) ->
             (a'₅ ≤ 255) ->
              ((j₀ < len₀)) ∧
              (∀ (a'₆ : Int),
               ((k4 a'₆ len₀ i₀ j₀ a'₅))) ∧
              (∀ (a'₇ : Int),
               ((k4 a'₇ len₀ i₀ j₀ a'₅)) ->
                (a'₇ ≥ 0) ->
                 (a'₇ ≤ 255) ->
                  ((a'₅ ≠ a'₇) ->
                   ((j₀ ≠ 0) ->
                    ((((j₀ - 1) ≥ 0)) ∧
                    (((j₀ - 1) ≤ 18446744073709551615))
                    ) ∧
                    (((j₀ - 1) < len₀)) ∧
                    (∀ (a'₈ : Int),
                     ((k2 a'₈ i₀ j₀ len₀)) ->
                      ((k5 a'₈ len₀ i₀ j₀ a'₅ a'₇))) ∧
                    (∀ (a'₉ : Int),
                     ((k5 a'₉ len₀ i₀ j₀ a'₅ a'₇)) ->
                      (a'₉ ≥ 0) ->
                       (a'₉ ≤ 18446744073709551615) ->
                        (((k6 i₀ a'₉ len₀ i₀ j₀ a'₅ a'₇))) ∧
                        (∀ (a'₁₀ : Int),
                         ((k2 a'₁₀ i₀ j₀ len₀)) ->
                          ((k7 a'₁₀ i₀ a'₉ len₀ i₀ j₀ a'₅ a'₇)))
                        )
                    ) ∧
                   ((¬(j₀ ≠ 0)) ->
                    (∀ (a'₁₁ : Int),
                     ((k2 a'₁₁ i₀ j₀ len₀)) ->
                      ((k8 a'₁₁ len₀ i₀ j₀ a'₅ a'₇))) ∧
                    (((k8 0 len₀ i₀ j₀ a'₅ a'₇))) ∧
                    ((((i₀ + 1) ≥ 0)) ∧
                    (((i₀ + 1) ≤ 18446744073709551615))
                    ) ∧
                    (((k6 (i₀ + 1) j₀ len₀ i₀ j₀ a'₅ a'₇))) ∧
                    (∀ (a'₁₂ : Int),
                     ((k8 a'₁₂ len₀ i₀ j₀ a'₅ a'₇)) ->
                      ((k7 a'₁₂ (i₀ + 1) j₀ len₀ i₀ j₀ a'₅ a'₇)))
                    ) ∧
                   (∀ (i₁ : Int),
                    ∀ (j₁ : Int),
                     ((k6 i₁ j₁ len₀ i₀ j₀ a'₅ a'₇)) ->
                      (((k9 i₁ j₁ len₀ i₀ j₀ a'₅ a'₇))) ∧
                      (∀ (a'₁₅ : Int),
                       ((k7 a'₁₅ i₁ j₁ len₀ i₀ j₀ a'₅ a'₇)) ->
                        ((k10 a'₁₅ i₁ j₁ len₀ i₀ j₀ a'₅ a'₇)))
                      )
                   ) ∧
                  ((¬(a'₅ ≠ a'₇)) ->
                   (∀ (a'₁₆ : Int),
                    ((k2 a'₁₆ i₀ j₀ len₀)) ->
                     ((k11 a'₁₆ len₀ i₀ j₀ a'₅ a'₇))) ∧
                   ((((j₀ + 1) ≥ 0)) ∧
                   (((j₀ + 1) ≤ 18446744073709551615))
                   ) ∧
                   (((k11 (j₀ + 1) len₀ i₀ j₀ a'₅ a'₇))) ∧
                   ((((i₀ + 1) ≥ 0)) ∧
                   (((i₀ + 1) ≤ 18446744073709551615))
                   ) ∧
                   ((((j₀ + 1) ≥ 0)) ∧
                   (((j₀ + 1) ≤ 18446744073709551615))
                   ) ∧
                   (((k9 (i₀ + 1) (j₀ + 1) len₀ i₀ j₀ a'₅ a'₇))) ∧
                   (∀ (a'₁₇ : Int),
                    ((k11 a'₁₇ len₀ i₀ j₀ a'₅ a'₇)) ->
                     ((k10 a'₁₇ (i₀ + 1) (j₀ + 1) len₀ i₀ j₀ a'₅ a'₇)))
                   ) ∧
                  (∀ (i₂ : Int),
                   ∀ (j₂ : Int),
                    ((k9 i₂ j₂ len₀ i₀ j₀ a'₅ a'₇)) ->
                     (((k1 i₂ j₂ len₀))) ∧
                     (∀ (a'₂₀ : Int),
                      ((k10 a'₂₀ i₂ j₂ len₀ i₀ j₀ a'₅ a'₇)) ->
                       ((k2 a'₂₀ i₂ j₂ len₀)))
                     )
                  )
              )
          )
         )
      )
      
end F
