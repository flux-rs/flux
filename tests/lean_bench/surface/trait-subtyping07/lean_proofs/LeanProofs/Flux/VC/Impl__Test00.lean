import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__Test00 := 
 ∀ (x₀ : Prop),
  (x₀ = (if x₀ then (x₀ ∧ x₀) else x₀))
end F
