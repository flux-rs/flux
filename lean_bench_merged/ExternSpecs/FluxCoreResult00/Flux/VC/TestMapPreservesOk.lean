import ExternSpecs.FluxCoreResult00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestMapPreservesOk := 
 ∀ (r₀ : Prop),
  ((r₀ = r₀) = True)
end F
