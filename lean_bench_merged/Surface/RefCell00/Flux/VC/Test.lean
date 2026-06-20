import Surface.RefCell00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (∀ (v₀ : Int),
  (v₀ ≥ 0) ->
   ((k0 v₀))) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0)) ∧
 (∀ (a'₂ : Int),
  ((k0 a'₂)) ->
   ((k1 a'₂))) ∧
 (∀ (a'₃ : Int),
  ((k1 a'₃)) ->
   ((k0 a'₃))) ∧
 (∀ (a'₄ : Int),
  ((k1 a'₄)) ->
   (a'₄ ≥ 0))
 
end F
