import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IntAdd := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (((b₀ + a₀) > 0) ∧ ((b₀ + a₀) < 1000000000)) ->
    (a₀ ≥ (-2147483648)) ->
     (a₀ ≤ 2147483647) ->
      (b₀ ≥ (-2147483648)) ->
       (b₀ ≤ 2147483647) ->
        (((a₀ + b₀) ≥ (-2147483648))) ∧
        (((a₀ + b₀) ≤ 2147483647))
        
end F
