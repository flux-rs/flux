import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Baz := 
 ∀ (s₀ : Int),
  (s₀ > 10) ->
   (9 < s₀)
end F
