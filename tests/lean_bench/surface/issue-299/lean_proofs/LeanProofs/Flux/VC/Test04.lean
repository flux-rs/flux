import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.S2
import LeanFixpoint
open Classical

namespace F



def Test04 := 
 ∀ (x₀ : Int),
  (x₀ = 10) ->
   ∀ (a'₁ : S2),
    ∀ (a'₂ : Int),
     ((S2.b a'₁) > 0) ->
      ∀ (v₀ : Int),
       (v₀ > 0) ->
        ((v₀ + 1) > 0)
end F
