import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (n₀ : Int),
  ∀ (b₀ : Prop),
   (2 ≤ n₀) ->
    (0 ≤ n₀) ->
     ((¬b₀) ->
      (1 < n₀)) ∧
     (b₀ ->
      (0 < n₀))
     
end F
