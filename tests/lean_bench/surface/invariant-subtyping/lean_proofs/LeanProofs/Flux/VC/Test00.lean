import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ = 0)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   ((k0 a'₁)))
 
end F
