import ExternSpecs.FluxCorePtr00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ReadIx := 
 ∀ (base₀ : Int),
  ∀ (addr₀ : Int),
   ∀ (size₀ : Int),
    ((addr₀ ≥ base₀) ∧ (size₀ = 10)) ->
     (size₀ > 0)
end F
