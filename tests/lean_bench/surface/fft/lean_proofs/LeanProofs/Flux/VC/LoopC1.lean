import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def LoopC1 := 
 ∀ (k₀ : Int),
  ∀ (j₀ : Int),
   (j₀ ≥ 0) ->
    (k₀ ≥ 0) ->
     ((¬(j₀ ≤ k₀)) ->
      (((j₀ - k₀) ≥ 0)) ∧
      (∀ (v₀ : Int),
       (v₀ ≤ ((k₀ / 2) + (k₀ / 2))) ->
        (v₀ ≥ 0) ->
         (v₀ ≤ (k₀ + k₀)))
      ) ∧
     ((j₀ ≤ k₀) ->
      ((j₀ + k₀) ≤ (k₀ + k₀)))
     
end F
