import Surface.Kmeans.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def InitCenters := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   (k₀ > 0) ->
    (n₀ ≥ 0) ->
     (k₀ ≥ 0) ->
      (((k0 0 0 n₀ k₀))) ∧
      (∀ (res₀ : Int),
       ∀ (i₀ : Int),
        ((k0 res₀ i₀ n₀ k₀)) ->
         ((¬(i₀ < k₀)) ->
          (∀ (a'₂ : Int),
           ((k1 a'₂ res₀ i₀ n₀ k₀)) ->
            (a'₂ = n₀)) ∧
          ((res₀ = k₀))
          ) ∧
         ((i₀ < k₀) ->
          (0 ≤ n₀) ->
           (∀ (a'₃ : Int),
            ((k1 a'₃ res₀ i₀ n₀ k₀)) ->
             ((k2 a'₃ n₀ k₀ res₀ i₀))) ∧
           (((k2 n₀ n₀ k₀ res₀ i₀))) ∧
           ((0 ≤ (res₀ + 1)) ->
            (((k0 (res₀ + 1) (i₀ + 1) n₀ k₀))) ∧
            (∀ (a'₄ : Int),
             ((k2 a'₄ n₀ k₀ res₀ i₀)) ->
              ((k1 a'₄ (res₀ + 1) (i₀ + 1) n₀ k₀)))
            )
           )
         )
      
end F
