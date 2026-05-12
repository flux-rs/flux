import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def ModSignedPos := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (a₀ ≥ 0) ->
    (b₀ > 0) ->
     ((b₀ ≠ 0)) ∧
     ((b₀ ≠ 0) ->
      ((¬((b₀ = (-1)) ∧ (a₀ = (-2147483648))))) ∧
      ((¬((b₀ = (-1)) ∧ (a₀ = (-2147483648)))) ->
       ∀ (a'₀ : Int),
        ((b₀ ≥ 0) -> (a'₀ = (a₀ % b₀))) ->
         (a'₀ = (a₀ % b₀)))
      )
     
end F
