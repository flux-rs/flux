import Surface.AbstractRefinementInCompositeSort.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Direct := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  (((k0 a'₀)) ->
   (a'₀ ≥ 0)) ∧
  ((a'₀ ≥ 0) ->
   ((k0 a'₀)))
  )
 
end F
