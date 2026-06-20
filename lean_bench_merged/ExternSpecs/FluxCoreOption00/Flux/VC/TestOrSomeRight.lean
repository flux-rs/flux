import ExternSpecs.FluxCoreOption00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestOrSomeRight := 
 ∀ (x₀ : Prop),
  ((x₀ ∨ True) = True)
end F
