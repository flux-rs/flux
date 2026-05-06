import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestExiR := ∃ k0 : (a0 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ((n₀ ≠ 0) ->
   ((n₀ ≠ 1) ->
    ((n₀ ≠ 2) ->
     ((n₀ = 3) = ((((0 = n₀) ∨ (1 = n₀)) ∨ (2 = n₀)) ∨ (3 = n₀)))) ∧
    ((¬(n₀ ≠ 2)) ->
     ((k0 n₀)))
    ) ∧
   ((¬(n₀ ≠ 1)) ->
    ((k0 n₀)))
   ) ∧
  ((¬(n₀ ≠ 0)) ->
   ((k0 n₀))) ∧
  (((k0 n₀)) ->
   (True = ((((0 = n₀) ∨ (1 = n₀)) ∨ (2 = n₀)) ∨ (3 = n₀))))
  
end F
