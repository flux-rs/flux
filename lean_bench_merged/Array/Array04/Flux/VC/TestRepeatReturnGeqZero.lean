import Array.Array04.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestRepeatReturnGeqZero := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ ≥ 0))
 
end F
