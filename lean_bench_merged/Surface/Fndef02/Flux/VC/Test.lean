import Surface.Fndef02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((a'₀ > 0)) ∧
   (((k1 (1 / a'₀))))
   ) ∧
 (((k0 10))) ∧
 (∀ (a'₁ : Int),
  ((k1 a'₁)) ->
   (a'₁ = 0))
 
end F
