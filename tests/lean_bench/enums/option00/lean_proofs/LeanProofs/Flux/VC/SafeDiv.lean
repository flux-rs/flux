import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def SafeDiv := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (numerator₀ : Int),
  ∀ (denominator₀ : Int),
   (numerator₀ ≥ 0) ->
    (denominator₀ ≥ 0) ->
     ((denominator₀ ≠ 0) ->
      ((denominator₀ ≠ 0)) ∧
      ((denominator₀ ≠ 0) ->
       (((k0 (numerator₀ / denominator₀) numerator₀ denominator₀))) ∧
       (∀ (a'₀ : Int),
        ((k0 a'₀ numerator₀ denominator₀)) ->
         (a'₀ = (numerator₀ / denominator₀)))
       )
      ) ∧
     ((¬(denominator₀ ≠ 0)) ->
      (False = (denominator₀ ≠ 0)))
     
end F
