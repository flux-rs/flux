import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MinIndex := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (0 ≤ n₀) ->
    (n₀ ≥ 0) ->
     (((k0 0 0 n₀))) ∧
     (∀ (res₀ : Int),
      ∀ (i₀ : Int),
       ((k0 res₀ i₀ n₀)) ->
        ((¬(i₀ < n₀)) ->
         (res₀ < n₀)) ∧
        ((i₀ < n₀) ->
         (∀ (a'₂ : Int),
          ((k1 a'₂ n₀ res₀ i₀))) ∧
         (∀ (a'₃ : Int),
          ((k1 a'₃ n₀ res₀ i₀)) ->
           ((res₀ < n₀)) ∧
           (∀ (a'₄ : Int),
            ((k2 a'₄ n₀ res₀ i₀ a'₃))) ∧
           (∀ (a'₅ : Int),
            ((k2 a'₅ n₀ res₀ i₀ a'₃)) ->
             ((¬(a'₃ < a'₅)) ->
              ((k3 res₀ n₀ res₀ i₀ a'₃ a'₅))) ∧
             ((a'₃ < a'₅) ->
              ((k3 i₀ n₀ res₀ i₀ a'₃ a'₅))) ∧
             (∀ (a'₆ : Int),
              ((k3 a'₆ n₀ res₀ i₀ a'₃ a'₅)) ->
               ((k0 a'₆ (i₀ + 1) n₀)))
             )
           )
         )
        )
     
end F
