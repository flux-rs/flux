import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.Magic
open Classical
set_option linter.unusedVariables false


namespace F



def TestAllL := 
 ∀ (n₀ : Int),
  ((((magic 0 n₀) ∧ (magic 1 n₀)) ∧ (magic 2 n₀)) ∧ (magic 3 n₀)) ->
   (magic 3 n₀)
end F
