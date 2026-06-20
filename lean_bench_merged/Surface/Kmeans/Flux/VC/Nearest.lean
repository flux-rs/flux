import Surface.Kmeans.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Nearest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   (k₀ > 0) ->
    (0 ≤ n₀) ->
     (0 ≤ k₀) ->
      (k₀ ≥ 0) ->
       (((k0 0 0 n₀ k₀))) ∧
       (∀ (res₀ : Int),
        ∀ (i₀ : Int),
         ((k0 res₀ i₀ n₀ k₀)) ->
          ((¬(i₀ < k₀)) ->
           (res₀ < k₀)) ∧
          ((i₀ < k₀) ->
           (∀ (a'₂ : Int),
            (a'₂ = n₀) ->
             ((k1 a'₂ n₀ k₀ res₀ i₀))) ∧
           (∀ (a'₃ : Int),
            ((k1 a'₃ n₀ k₀ res₀ i₀)) ->
             (0 ≤ a'₃) ->
              ((n₀ = a'₃)) ∧
              (∀ (a'₄ : Prop),
               ((¬a'₄) ->
                ((k2 res₀ n₀ k₀ res₀ i₀ a'₃ a'₄))) ∧
               (a'₄ ->
                ((k2 i₀ n₀ k₀ res₀ i₀ a'₃ True))) ∧
               (∀ (res₁ : Int),
                ((k2 res₁ n₀ k₀ res₀ i₀ a'₃ a'₄)) ->
                 ((k0 res₁ (i₀ + 1) n₀ k₀)))
               )
              )
           )
          )
       
end F
