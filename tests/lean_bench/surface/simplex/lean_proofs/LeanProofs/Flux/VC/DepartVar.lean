import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DepartVar := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Prop) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ∀ (v₀ : Int),
    ∀ (v₁ : Int),
     ((0 < v₀) ∧ (v₀ < n₀)) ->
      ((0 < v₁) ∧ (v₁ < m₀)) ->
       (m₀ ≥ 0) ->
        (n₀ ≥ 0) ->
         (v₀ ≥ 0) ->
          (v₁ ≥ 0) ->
           (((k0 v₁ (v₁ + 1) m₀ n₀ v₀ v₁))) ∧
           (∀ (i₀ : Int),
            ∀ (i_₀ : Int),
             ((k0 i₀ i_₀ m₀ n₀ v₀ v₁)) ->
              ((¬(i_₀ < m₀)) ->
               ((0 < i₀)) ∧
               ((i₀ < m₀))
               ) ∧
              ((i_₀ < m₀) ->
               ∀ (a'₄ : Prop),
                ((¬a'₄) ->
                 ((k1 i₀ m₀ n₀ v₀ v₁ i₀ i_₀ a'₄))) ∧
                (a'₄ ->
                 (((n₀ - 1) ≥ 0)) ∧
                 (((n₀ - 1) < n₀)) ∧
                 (∀ (a'₅ : Prop),
                  ((¬a'₅) ->
                   ((k2 i₀ m₀ n₀ v₀ v₁ i₀ i_₀ True a'₅))) ∧
                  (a'₅ ->
                   ((k2 i_₀ m₀ n₀ v₀ v₁ i₀ i_₀ True True))) ∧
                  (∀ (i₁ : Int),
                   ((k2 i₁ m₀ n₀ v₀ v₁ i₀ i_₀ True a'₅)) ->
                    ((k1 i₁ m₀ n₀ v₀ v₁ i₀ i_₀ True)))
                  )
                 ) ∧
                (∀ (i₂ : Int),
                 ((k1 i₂ m₀ n₀ v₀ v₁ i₀ i_₀ a'₄)) ->
                  ((k0 i₂ (i_₀ + 1) m₀ n₀ v₀ v₁)))
                )
              )
           
end F
