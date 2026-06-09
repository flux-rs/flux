import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Normal := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (w₀ : Int),
   (0 ≤ n₀) ->
    (w₀ ≥ 0) ->
     (((k0 0 0 n₀ w₀))) ∧
     (∀ (i₀ : Int),
      ∀ (res₀ : Int),
       ((k0 i₀ res₀ n₀ w₀)) ->
        (n₀ ≥ 0) ->
         ((¬(i₀ < n₀)) ->
          (res₀ = n₀)) ∧
         ((i₀ < n₀) ->
          (0 ≤ (res₀ + 1)) ->
           ((k0 (i₀ + 1) (res₀ + 1) n₀ w₀)))
         )
     
end F
