import Structs.EnumMatch02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 (5 + 7)))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (0 ≤ a'₀))
 
end F
