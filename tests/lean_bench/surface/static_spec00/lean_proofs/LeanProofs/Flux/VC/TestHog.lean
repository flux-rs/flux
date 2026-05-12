import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestHog := 
 ∀ (v₀ : Int),
  (v₀ ≥ 0) ->
   (v₀ < 100) ->
    ∀ (v₁ : Int),
     (v₁ ≥ 0) ->
      (v₁ < 100) ->
       ∀ (v₂ : Int),
        (v₂ ≥ 0) ->
         (v₂ < 100) ->
          (((v₀ + v₁) + v₂) < 300)
end F
