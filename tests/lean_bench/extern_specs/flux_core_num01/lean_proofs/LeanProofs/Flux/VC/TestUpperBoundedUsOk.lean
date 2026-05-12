import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl3MAX
import LeanFixpoint
open Classical

namespace F



def TestUpperBoundedUsOk := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (True -> (a'₁ = 9223372036854775807)) ->
      (x₀ ≤ a'₁) ->
       ((x₀ ≤ num_impl_3_MAX) = True)
end F
