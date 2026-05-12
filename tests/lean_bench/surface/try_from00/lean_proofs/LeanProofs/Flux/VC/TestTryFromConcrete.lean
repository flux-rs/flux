import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestTryFromConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (v₀ : Int),
  (42 = v₀) ->
   ((k0 v₀))) ∧
 (∀ (m₀ : Int),
  ((k0 m₀)) ->
   ((m₀ = 42) = True))
 
end F
