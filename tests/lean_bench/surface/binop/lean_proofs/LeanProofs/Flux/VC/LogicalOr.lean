import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def LogicalOr := 
 ∀ (a₀ : Prop),
  ∀ (b₀ : Prop),
   (((a₀ ∨ b₀) = a₀) ∨ ((a₀ ∨ b₀) = b₀))
end F
