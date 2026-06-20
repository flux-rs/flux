import ExternSpecs.FluxCoreOption00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestOkOrElseBranch := 
 ∀ (x₀ : Prop),
  ((x₀ = x₀) = True)
end F
