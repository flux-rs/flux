import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Doit := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 16 4))) ∧
 (∀ (np₀ : Int),
  ∀ (i₀ : Int),
   ((k0 np₀ i₀)) ->
    (i₀ ≤ 16) ->
     ((np₀ ≥ 2)) ∧
     (((k0 (np₀ * 2) (i₀ + 1))))
     )
 
end F
