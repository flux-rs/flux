import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestUnwrapAfterCheck := 
 ∀ (r₀ : Prop),
  (¬r₀) ->
   (r₀ = False)
end F
