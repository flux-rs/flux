import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestForeach := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (((0 ≤ a'₀) = True)) ∧
   (((a'₀ < 10) = True))
   ) ∧
 (∀ (item₀ : Int),
  ((0 ≤ item₀) ∧ (item₀ < 10)) ->
   ((k0 item₀)))
 
end F
