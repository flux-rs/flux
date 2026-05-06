import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__New := 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≤ hi₀) ->
    (lo₀ ≤ lo₀)
end F
