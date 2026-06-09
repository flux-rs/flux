import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestOptSpecs := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (((k0 42))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (∀ (c₀ : Int),
  ((k1 c₀)) ->
   ((c₀ = 42) = True))
 
end F
