import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


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
