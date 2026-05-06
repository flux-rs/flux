import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IsSomeFlip := 
 ∀ (b₀ : Prop),
  ((b₀ = False) ->
   (False = b₀)) ∧
  ((b₀ = True) ->
   (True = b₀))
  
end F
