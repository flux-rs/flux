import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def FibLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (0 < v₀) ->
   (((k0 1 1 v₀ v₀))) ∧
   (∀ (i₀ : Int),
    ∀ (j₀ : Int),
     ∀ (k₀ : Int),
      ((k0 i₀ j₀ k₀ v₀)) ->
       ((¬(k₀ > 2)) ->
        (0 < i₀)) ∧
       ((k₀ > 2) ->
        ((k0 (i₀ + j₀) i₀ (k₀ - 1) v₀)))
       )
   
end F
