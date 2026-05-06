import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOk := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 (a'₀ + 1)))) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 99) ->
   ((k0 a'₁))) ∧
 (∀ (a'₂ : Int),
  ((k1 a'₂)) ->
   (a'₂ = 100))
 
end F
