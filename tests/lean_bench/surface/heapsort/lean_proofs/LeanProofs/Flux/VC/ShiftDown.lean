import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ShiftDown := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (len₀ : Int),
  ∀ (v₀ : Int),
   ∀ (v₁ : Int),
    (v₀ < len₀) ->
     (v₁ < len₀) ->
      (0 ≤ len₀) ->
       (v₀ ≥ 0) ->
        (v₁ ≥ 0) ->
         (((k0 v₀ len₀ v₀ v₁))) ∧
         (∀ (root₀ : Int),
          ((k0 root₀ len₀ v₀ v₁)) ->
           (¬(((root₀ * 2) + 1) > v₁)) ->
            ((¬((((root₀ * 2) + 1) + 1) ≤ v₁)) ->
             ((k1 ((root₀ * 2) + 1) len₀ v₀ v₁ root₀))) ∧
            (((((root₀ * 2) + 1) + 1) ≤ v₁) ->
             ((((root₀ * 2) + 1) < len₀)) ∧
             (∀ (a'₃ : Int),
              ((k2 a'₃ len₀ v₀ v₁ root₀))) ∧
             (∀ (a'₄ : Int),
              ((k2 a'₄ len₀ v₀ v₁ root₀)) ->
               (((((root₀ * 2) + 1) + 1) < len₀)) ∧
               (∀ (a'₅ : Int),
                ((k3 a'₅ len₀ v₀ v₁ root₀ a'₄))) ∧
               (∀ (a'₆ : Int),
                ((k3 a'₆ len₀ v₀ v₁ root₀ a'₄)) ->
                 ((¬(a'₄ < a'₆)) ->
                  ((k4 ((root₀ * 2) + 1) len₀ v₀ v₁ root₀ a'₄ a'₆))) ∧
                 ((a'₄ < a'₆) ->
                  ((k4 (((root₀ * 2) + 1) + 1) len₀ v₀ v₁ root₀ a'₄ a'₆))) ∧
                 (∀ (child₀ : Int),
                  ((k4 child₀ len₀ v₀ v₁ root₀ a'₄ a'₆)) ->
                   ((k1 child₀ len₀ v₀ v₁ root₀)))
                 )
               )
             ) ∧
            (∀ (child₁ : Int),
             ((k1 child₁ len₀ v₀ v₁ root₀)) ->
              ((root₀ < len₀)) ∧
              (∀ (a'₉ : Int),
               ((k5 a'₉ len₀ v₀ v₁ root₀ child₁))) ∧
              (∀ (a'₁₀ : Int),
               ((k5 a'₁₀ len₀ v₀ v₁ root₀ child₁)) ->
                ((child₁ < len₀)) ∧
                (∀ (a'₁₁ : Int),
                 ((k6 a'₁₁ len₀ v₀ v₁ root₀ child₁ a'₁₀))) ∧
                (∀ (a'₁₂ : Int),
                 ((k6 a'₁₂ len₀ v₀ v₁ root₀ child₁ a'₁₀)) ->
                  (a'₁₀ < a'₁₂) ->
                   ((root₀ < len₀)) ∧
                   ((child₁ < len₀)) ∧
                   (((k0 child₁ len₀ v₀ v₁)))
                   )
                )
              )
            )
         
end F
