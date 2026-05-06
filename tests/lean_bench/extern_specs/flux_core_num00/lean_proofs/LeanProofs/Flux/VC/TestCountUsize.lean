import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#11}BITS
import LeanFixpoint
open Classical

namespace F



def TestCountUsize := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ ≤ num_{impl#11}_BITS) ->
     (v₀ ≥ 0) ->
      (((v₀ ≤ 64) = True)) ∧
      (∀ (v₁ : Int),
       (v₁ ≤ num_{impl#11}_BITS) ->
        (v₁ ≥ 0) ->
         (((v₁ ≤ 64) = True)) ∧
         (∀ (v₂ : Int),
          (v₂ ≤ num_{impl#11}_BITS) ->
           (v₂ ≥ 0) ->
            (((v₂ ≤ 64) = True)) ∧
            (∀ (v₃ : Int),
             (v₃ ≤ num_{impl#11}_BITS) ->
              (v₃ ≥ 0) ->
               (((v₃ ≤ 64) = True)) ∧
               (∀ (v₄ : Int),
                (v₄ ≤ num_{impl#11}_BITS) ->
                 (v₄ ≥ 0) ->
                  (((v₄ ≤ 64) = True)) ∧
                  (∀ (v₅ : Int),
                   (v₅ ≤ num_{impl#11}_BITS) ->
                    (v₅ ≥ 0) ->
                     ((v₅ ≤ 64) = True))
                  )
               )
            )
         )
      
end F
