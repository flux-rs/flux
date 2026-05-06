import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestExpectErrAfterCheck := 
 ∀ (r₀ : Prop),
  (¬r₀) ->
   (r₀ = False)
end F
