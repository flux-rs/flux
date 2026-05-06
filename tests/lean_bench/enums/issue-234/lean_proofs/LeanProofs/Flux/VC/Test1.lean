import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (x₀ : Int),
  ((x₀ = 2) ->
   (2 = x₀)) ∧
  ((x₀ = 3) ->
   (3 = x₀)) ∧
  ((x₀ = 1) ->
   (1 = x₀))
  
end F
