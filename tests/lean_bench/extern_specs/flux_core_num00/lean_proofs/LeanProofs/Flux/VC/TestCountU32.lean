import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8BITS
import LeanFixpoint
open Classical

namespace F



def TestCountU32 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ ≤ num_impl_8_BITS) ->
     (v₀ ≥ 0) ->
      (((v₀ ≤ 32) = True)) ∧
      (∀ (v₁ : Int),
       (v₁ ≤ num_impl_8_BITS) ->
        (v₁ ≥ 0) ->
         (((v₁ ≤ 32) = True)) ∧
         (∀ (v₂ : Int),
          (v₂ ≤ num_impl_8_BITS) ->
           (v₂ ≥ 0) ->
            (((v₂ ≤ 32) = True)) ∧
            (∀ (v₃ : Int),
             (v₃ ≤ num_impl_8_BITS) ->
              (v₃ ≥ 0) ->
               (((v₃ ≤ 32) = True)) ∧
               (∀ (v₄ : Int),
                (v₄ ≤ num_impl_8_BITS) ->
                 (v₄ ≥ 0) ->
                  (((v₄ ≤ 32) = True)) ∧
                  (∀ (v₅ : Int),
                   (v₅ ≤ num_impl_8_BITS) ->
                    (v₅ ≥ 0) ->
                     ((v₅ ≤ 32) = True))
                  )
               )
            )
         )
      
end F
