import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOrSomeRight := 
 ∀ (x₀ : Prop),
  ((x₀ ∨ True) = True)
end F
