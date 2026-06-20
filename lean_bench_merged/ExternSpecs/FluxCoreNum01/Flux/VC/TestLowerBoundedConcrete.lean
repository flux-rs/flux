import ExternSpecs.FluxCoreNum01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestLowerBoundedConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 100) ->
   ((k0 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    ((a'₁ = 100) = True))
 
end F
