import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Fill := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (a'₁ : Int),
     ((k0 i₀ a'₁ n₀)) ->
      ((¬(i₀ < n₀)) ->
       (a'₁ = n₀)) ∧
      ((i₀ < n₀) ->
       ∀ (a'₂ : Int),
        ((a'₁ < n₀)) ∧
        (((k0 (i₀ + 1) (a'₁ + 1) n₀)))
        )
      )
   
end F
