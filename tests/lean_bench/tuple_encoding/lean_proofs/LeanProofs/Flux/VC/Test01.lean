import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.S
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ∀ (a'₀ : S),
  (((S.x a'₀) = (S.x a'₀))) ∧
  (((S.y a'₀) = (S.y a'₀)))
  
end F
