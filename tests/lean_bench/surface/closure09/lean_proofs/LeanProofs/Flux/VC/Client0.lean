import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Client0 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 (a'₀ + 1) a'₀))) ∧
 (∀ (king₀ : Int),
  (((k0 king₀))) ∧
  (∀ (a'₂ : Int),
   ((k1 a'₂ king₀)) ->
    (a'₂ = (king₀ + 1)))
  )
 
end F
