import Structs.DepField00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ∀ (k₀ : Int),
  (k₀ < (k₀ + 1))
end F
