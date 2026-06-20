import Surface.TryFrom00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestTryFromConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (v₀ : Int),
  (42 = v₀) ->
   ((k0 v₀))) ∧
 (∀ (m₀ : Int),
  ((k0 m₀)) ->
   ((m₀ = 42) = True))
 
end F
