import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__Len := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ = 0) ->
    (0 = n₀)) ∧
   (∀ (n₁ : Int),
    (n₀ = (n₁ + 1)) ->
     (n₁ ≥ 0) ->
      ∀ (a'₁ : Int),
       ((1 + n₁) = n₀))
   
end F
