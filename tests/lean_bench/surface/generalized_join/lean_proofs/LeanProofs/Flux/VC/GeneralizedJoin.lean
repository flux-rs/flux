import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def GeneralizedJoin := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 0 0 n₀))) ∧
  (∀ (j₀ : Int),
   ∀ (i₀ : Int),
    ((k0 j₀ i₀ n₀)) ->
     ((¬(i₀ < n₀)) ->
      ((i₀ - j₀) = 0)) ∧
     ((i₀ < n₀) ->
      ((k0 (j₀ + 1) (i₀ + 1) n₀)))
     )
  
end F
