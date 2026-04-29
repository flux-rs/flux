import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 0 0))) ∧
 (∀ (res₀ : Int),
  ∀ (i₀ : Int),
   ((k0 res₀ i₀)) ->
    ((¬(i₀ < 100)) ->
     (0 ≤ res₀)) ∧
    ((i₀ < 100) ->
     ((k0 (res₀ + 1) (i₀ + 1))))
    )
 
end F
