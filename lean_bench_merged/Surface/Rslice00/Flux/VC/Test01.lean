import Surface.Rslice00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (((n₀ % 2) = 0) ∧ (n₀ > 0)) ->
    (n₀ ≥ 0) ->
     ((((n₀ / 2) - 1) ≥ 0)) ∧
     (((0 ≤ ((n₀ / 2) - 1))) ∧
     ((((n₀ / 2) - 1) < n₀))
     ) ∧
     ((((n₀ - 1) ≥ 0)) ∧
     ((((n₀ / 2) ≤ (n₀ - 1))) ∧
     (((n₀ - 1) < n₀)) ∧
     (((((n₀ / 2) - 1) < (n₀ / 2)) ∨ ((n₀ - 1) < 0)))
     ) ∧
     ((((((n₀ / 2) - 1) - 0) + 1) ≥ 0) ->
      ((((n₀ - 1) - (n₀ / 2)) + 1) ≥ 0) ->
       ((((n₀ - 1) - (n₀ / 2)) + 1) = ((((n₀ / 2) - 1) - 0) + 1)))
     )
     
end F
