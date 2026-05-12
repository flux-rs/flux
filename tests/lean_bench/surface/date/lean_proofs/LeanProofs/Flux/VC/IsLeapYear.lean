import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IsLeapYear := ∃ k0 : (a0 : Prop) -> (a1 : Int) -> Prop, 
 ∀ (y₀ : Int),
  (y₀ ≥ 0) ->
   (((y₀ % 400) ≠ 0) ->
    (((y₀ % 4) ≠ 0) ->
     ((k0 False y₀))) ∧
    ((¬((y₀ % 4) ≠ 0)) ->
     ((k0 ((y₀ % 100) ≠ 0) y₀))) ∧
    (∀ (a'₀ : Prop),
     ((k0 a'₀ y₀)) ->
      (a'₀ = (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0)))))
    ) ∧
   ((¬((y₀ % 400) ≠ 0)) ->
    (True = (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0)))))
   
end F
