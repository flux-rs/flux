import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

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
           (((k0 (v₁ + 1) v₁ m₀ n₀ v₀ v₁))) ∧
           (∀ (i_₀ : Int),
            ∀ (i₀ : Int),
             ((k0 i_₀ i₀ m₀ n₀ v₀ v₁)) ->
              ((¬(i_₀ < m₀)) ->
               ((0 < i₀)) ∧
               ((i₀ < m₀))
               ) ∧
              ((i_₀ < m₀) ->
               ∀ (a'₄ : Prop),
                ((¬a'₄) ->
                 ((k1 i₀ m₀ n₀ v₀ v₁ i_₀ i₀ a'₄))) ∧
                (a'₄ ->
                 (((n₀ - 1) ≥ 0)) ∧
                 (((n₀ - 1) < n₀)) ∧
                 (∀ (a'₅ : Prop),
                  ((¬a'₅) ->
                   ((k2 i₀ m₀ n₀ v₀ v₁ i_₀ i₀ True a'₅))) ∧
                  (a'₅ ->
                   ((k2 i_₀ m₀ n₀ v₀ v₁ i_₀ i₀ True True))) ∧
                  (∀ (i₁ : Int),
                   ((k2 i₁ m₀ n₀ v₀ v₁ i_₀ i₀ True a'₅)) ->
                    ((k1 i₁ m₀ n₀ v₀ v₁ i_₀ i₀ True)))
                  )
                 ) ∧
                (∀ (i₂ : Int),
                 ((k1 i₂ m₀ n₀ v₀ v₁ i_₀ i₀ a'₄)) ->
                  ((k0 (i_₀ + 1) i₂ m₀ n₀ v₀ v₁)))
                )
              )
           
end F
