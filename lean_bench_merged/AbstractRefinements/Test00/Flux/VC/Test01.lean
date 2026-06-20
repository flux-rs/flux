import AbstractRefinements.Test00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, 
 ((((k0 4))) ∧
 (((k0 10)))
 ) ∧
 (∀ (v₀ : Int),
  (((k0 v₀)) ∧ (v₀ ≥ 4) ∧ (v₀ ≥ 10)) ->
   (v₀ = 10))
 
end F
