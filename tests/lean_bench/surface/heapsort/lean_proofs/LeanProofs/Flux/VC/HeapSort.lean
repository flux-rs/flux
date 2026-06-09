import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def HeapSort := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (¬(n₀ ≤ 0)) ->
     (((k0 (n₀ / 2) n₀))) ∧
     (∀ (start₀ : Int),
      ((k0 start₀ n₀)) ->
       ((¬(start₀ > 0)) ->
        (((k1 n₀ n₀ start₀))) ∧
        (∀ (end₀ : Int),
         ((k1 end₀ n₀ start₀)) ->
          (end₀ > 1) ->
           (((end₀ - 1) ≥ 0)) ∧
           ((0 < n₀)) ∧
           (((end₀ - 1) < n₀)) ∧
           ((((end₀ - 1) - 1) ≥ 0)) ∧
           ((0 < n₀)) ∧
           ((((end₀ - 1) - 1) < n₀)) ∧
           (∀ (a'₂ : Int),
            ((k1 (end₀ - 1) n₀ start₀)))
           )
        ) ∧
       ((start₀ > 0) ->
        (((start₀ - 1) ≥ 0)) ∧
        (((n₀ - 1) ≥ 0)) ∧
        (((start₀ - 1) < n₀)) ∧
        (((n₀ - 1) < n₀)) ∧
        (∀ (a'₃ : Int),
         ((k0 (start₀ - 1) n₀)))
        )
       )
     
end F
