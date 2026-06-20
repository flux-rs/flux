import Surface.Kmeans.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansStep := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   ∀ (ps₀ : Int),
    (k₀ > 0) ->
     (n₀ ≥ 0) ->
      (0 ≤ k₀) ->
       (0 ≤ ps₀) ->
        (k₀ ≥ 0) ->
         ((k₀ > 0)) ∧
         ((((k0 0 n₀ k₀ ps₀))) ∧
         ((((k1 0 n₀ k₀ ps₀))) ∧
         (∀ (a'₁ : Int),
          (a'₁ = n₀) ->
           ((k2 a'₁ 0 n₀ k₀ ps₀))) ∧
         (∀ (a'₂ : Int),
          ((k0 a'₂ n₀ k₀ ps₀)) ->
           ((k3 a'₂ 0 n₀ k₀ ps₀))) ∧
         (∀ (i₀ : Int),
          ((k1 i₀ n₀ k₀ ps₀)) ->
           (ps₀ ≥ 0) ->
            ((¬(i₀ < ps₀)) ->
             ∀ (a'₄ : Int),
              ((k2 a'₄ i₀ n₀ k₀ ps₀)) ->
               (a'₄ = n₀)) ∧
            ((i₀ < ps₀) ->
             (∀ (a'₅ : Int),
              (a'₅ = n₀) ->
               ((k4 a'₅ n₀ k₀ ps₀ i₀))) ∧
             (∀ (a'₆ : Int),
              ((k4 a'₆ n₀ k₀ ps₀ i₀)) ->
               (0 ≤ a'₆) ->
                (∀ (a'₇ : Int),
                 (a'₇ = n₀) ->
                  (a'₇ = a'₆)) ∧
                (∀ (j₀ : Int),
                 (j₀ < k₀) ->
                  (j₀ ≥ 0) ->
                   (∀ (a'₉ : Int),
                    ((k2 a'₉ i₀ n₀ k₀ ps₀)) ->
                     ((k5 a'₉ n₀ k₀ ps₀ i₀ a'₆ j₀))) ∧
                   (∀ (a'₁₀ : Int),
                    (a'₁₀ = n₀) ->
                     ((k6 a'₁₀ n₀ k₀ ps₀ i₀ a'₆ j₀))) ∧
                   (∀ (a'₁₁ : Int),
                    ((k6 a'₁₁ n₀ k₀ ps₀ i₀ a'₆ j₀)) ->
                     (0 ≤ a'₁₁) ->
                      ∀ (a'₁₂ : Int),
                       ((k5 a'₁₂ n₀ k₀ ps₀ i₀ a'₆ j₀)) ->
                        ((a'₁₁ = a'₁₂)) ∧
                        (∀ (a'₁₃ : Int),
                         (∀ (a'₁₄ : Int),
                          ((k3 a'₁₄ i₀ n₀ k₀ ps₀)) ->
                           ((k7 a'₁₄ n₀ k₀ ps₀ i₀ a'₆ j₀ a'₁₁ a'₁₂ a'₁₃))) ∧
                         (∀ (a'₁₅ : Int),
                          (a'₁₅ ≥ 0) ->
                           ((k7 a'₁₅ n₀ k₀ ps₀ i₀ a'₆ j₀ a'₁₁ a'₁₂ a'₁₃)) ->
                            (((k7 (a'₁₅ + 1) n₀ k₀ ps₀ i₀ a'₆ j₀ a'₁₁ a'₁₂ a'₁₃))) ∧
                            (((k1 (i₀ + 1) n₀ k₀ ps₀))) ∧
                            (∀ (a'₁₆ : Int),
                             ((k5 a'₁₆ n₀ k₀ ps₀ i₀ a'₆ j₀)) ->
                              ((k2 a'₁₆ (i₀ + 1) n₀ k₀ ps₀))) ∧
                            (∀ (a'₁₇ : Int),
                             ((k7 a'₁₇ n₀ k₀ ps₀ i₀ a'₆ j₀ a'₁₁ a'₁₂ a'₁₃)) ->
                              ((k3 a'₁₇ (i₀ + 1) n₀ k₀ ps₀)))
                            )
                         )
                        )
                   )
                )
             )
            )
         )
         )
         
end F
