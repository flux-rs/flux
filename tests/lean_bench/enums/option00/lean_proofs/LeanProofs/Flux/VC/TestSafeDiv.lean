import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestSafeDiv := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (42 / 2)) ->
   ((k0 a'₀))) ∧
 (∀ (res₀ : Int),
  ((k0 res₀)) ->
   (res₀ ≥ 0) ->
    ((res₀ = 21) = True))
 
end F
