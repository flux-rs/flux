import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestRepeatWriteThenRead := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 42))) ∧
 ((((k0 100))) ∧
 (∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ((k0 a'₀)) ->
    (a'₀ ≥ 42))
 )
 
end F
