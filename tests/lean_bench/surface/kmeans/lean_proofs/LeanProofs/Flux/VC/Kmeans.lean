import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Kmeans := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   ∀ (ps₀ : Int),
    ∀ (iters₀ : Int),
     (k₀ > 0) ->
      (n₀ ≥ 0) ->
       (0 ≤ k₀) ->
        (0 ≤ ps₀) ->
         (((k0 0 n₀ k₀ ps₀ iters₀))) ∧
         (∀ (a'₂ : Int),
          (a'₂ = n₀) ->
           ((k1 a'₂ 0 n₀ k₀ ps₀ iters₀))) ∧
         (∀ (i₀ : Int),
          ((k0 i₀ n₀ k₀ ps₀ iters₀)) ->
           ((¬(i₀ < iters₀)) ->
            ∀ (a'₄ : Int),
             ((k1 a'₄ i₀ n₀ k₀ ps₀ iters₀)) ->
              (a'₄ = n₀)) ∧
           ((i₀ < iters₀) ->
            (∀ (a'₅ : Int),
             ((k1 a'₅ i₀ n₀ k₀ ps₀ iters₀)) ->
              (a'₅ = n₀)) ∧
            ((((k0 (i₀ + 1) n₀ k₀ ps₀ iters₀))) ∧
            (∀ (a'₆ : Int),
             (a'₆ = n₀) ->
              ((k1 a'₆ (i₀ + 1) n₀ k₀ ps₀ iters₀)))
            )
            )
           )
         
end F
