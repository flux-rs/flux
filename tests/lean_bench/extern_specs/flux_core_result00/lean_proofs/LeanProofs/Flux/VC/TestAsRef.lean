import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAsRef := 
 ∀ (r₀ : Prop),
  ((r₀ = r₀) = True)
end F
