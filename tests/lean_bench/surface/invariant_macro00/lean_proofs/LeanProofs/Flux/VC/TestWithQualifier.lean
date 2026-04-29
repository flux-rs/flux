import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestWithQualifier := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 n₀ n₀))) ∧
   (∀ (res₀ : Int),
    ∀ (i₀ : Int),
     ((k0 res₀ i₀ n₀)) ->
      ((¬(i₀ > 0)) ->
       (res₀ = n₀)) ∧
      ((i₀ > 0) ->
       (((i₀ - 1) ≥ 0)) ∧
       (((k0 (res₀ + 1) (i₀ - 1) n₀)))
       )
      )
   
end F
