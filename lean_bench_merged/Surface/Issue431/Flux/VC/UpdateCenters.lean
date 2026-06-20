import Surface.Issue431.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def UpdateCenters := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   ∀ (new_centers₀ : Int),
    (n₀ ≥ 0) ->
     (0 ≤ k₀) ->
      (0 ≤ new_centers₀) ->
       (∀ (v₀ : Int),
        (v₀ < k₀) ->
         ∀ (a'₂ : Int),
          (((k0 v₀ n₀ k₀ new_centers₀))) ∧
          (((k1 n₀ n₀ k₀ new_centers₀))) ∧
          (((k2 a'₂ n₀ k₀ new_centers₀)))
          ) ∧
       (((k3 n₀ k₀ new_centers₀))) ∧
       (∀ (a'₃ : Int),
        ((k0 a'₃ n₀ k₀ new_centers₀)) ->
         ∀ (a'₄ : Int),
          ((k1 a'₄ n₀ k₀ new_centers₀)) ->
           ∀ (a'₅ : Int),
            ((k2 a'₅ n₀ k₀ new_centers₀)) ->
             (((k4 a'₃ n₀ k₀ new_centers₀))) ∧
             (((k5 a'₄ n₀ k₀ new_centers₀))) ∧
             (((k6 a'₅ n₀ k₀ new_centers₀)))
             ) ∧
       (((k3 n₀ k₀ new_centers₀)) ->
        (∀ (a'₆ : Int),
         ((k4 a'₆ n₀ k₀ new_centers₀)) ->
          ∀ (a'₇ : Int),
           ((k5 a'₇ n₀ k₀ new_centers₀)) ->
            ∀ (a'₈ : Int),
             ((k6 a'₈ n₀ k₀ new_centers₀)) ->
              (((k7 a'₆ n₀ k₀ new_centers₀))) ∧
              (((k8 a'₇ n₀ k₀ new_centers₀))) ∧
              (((k9 a'₈ n₀ k₀ new_centers₀)))
              ) ∧
        (∀ (a'₉ : Int),
         ((k7 a'₉ n₀ k₀ new_centers₀)) ->
          ∀ (a'₁₀ : Int),
           ((k8 a'₁₀ n₀ k₀ new_centers₀)) ->
            ∀ (a'₁₁ : Int),
             ((k9 a'₁₁ n₀ k₀ new_centers₀)) ->
              (a'₉ ≥ 0) ->
               (0 ≤ a'₁₀) ->
                (a'₁₁ ≥ 0) ->
                 ((a'₉ < k₀)) ∧
                 (∀ (a'₁₂ : Int),
                  (a'₁₂ = n₀) ->
                   ((k10 a'₁₂ n₀ k₀ new_centers₀ a'₉ a'₁₀ a'₁₁))) ∧
                 (∀ (a'₁₃ : Int),
                  ((k10 a'₁₃ n₀ k₀ new_centers₀ a'₉ a'₁₀ a'₁₁)) ->
                   (a'₁₃ = n₀)) ∧
                 (((k10 a'₁₀ n₀ k₀ new_centers₀ a'₉ a'₁₀ a'₁₁))) ∧
                 (∀ (a'₁₄ : Int),
                  ((k7 a'₁₄ n₀ k₀ new_centers₀)) ->
                   ∀ (a'₁₅ : Int),
                    ((k8 a'₁₅ n₀ k₀ new_centers₀)) ->
                     ∀ (a'₁₆ : Int),
                      ((k9 a'₁₆ n₀ k₀ new_centers₀)) ->
                       (((k4 a'₁₄ n₀ k₀ new_centers₀))) ∧
                       (((k5 a'₁₅ n₀ k₀ new_centers₀))) ∧
                       (((k6 a'₁₆ n₀ k₀ new_centers₀)))
                       )
                 )
        )
       
end F
