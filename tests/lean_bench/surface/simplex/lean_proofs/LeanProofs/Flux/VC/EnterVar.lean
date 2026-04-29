import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def EnterVar := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   (m₀ > 0) ->
    (n₀ > 2) ->
     (m₀ ≥ 0) ->
      (n₀ ≥ 0) ->
       ((0 < m₀)) ∧
       ((1 < n₀)) ∧
       (((k0 1 2 m₀ n₀))) ∧
       (∀ (j₀ : Int),
        ∀ (j_₀ : Int),
         ((k0 j₀ j_₀ m₀ n₀)) ->
          (((n₀ - 1) ≥ 0)) ∧
          ((¬(j_₀ < (n₀ - 1))) ->
           ((0 < j₀)) ∧
           (((j₀ + 1) < n₀))
           ) ∧
          ((j_₀ < (n₀ - 1)) ->
           ((0 < m₀)) ∧
           ((j_₀ < n₀)) ∧
           (∀ (a'₂ : Prop),
            ((¬a'₂) ->
             ((k1 j₀ m₀ n₀ j₀ j_₀ a'₂))) ∧
            (a'₂ ->
             ((k1 j_₀ m₀ n₀ j₀ j_₀ True))) ∧
            (∀ (j₁ : Int),
             ((k1 j₁ m₀ n₀ j₀ j_₀ a'₂)) ->
              ((k0 j₁ (j_₀ + 1) m₀ n₀)))
            )
           )
          )
       
end F
