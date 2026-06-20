import ExternSpecs.FluxCoreNum00.Flux.Prelude
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl5BITS
open Classical
set_option linter.unusedVariables false


namespace F



def TestCountIsize := 
 ∀ (x₀ : Int),
  ∀ (v₀ : Int),
   (v₀ ≤ num_impl_5_BITS) ->
    (v₀ ≥ 0) ->
     (((v₀ ≤ 64) = True)) ∧
     (∀ (v₁ : Int),
      (v₁ ≤ num_impl_5_BITS) ->
       (v₁ ≥ 0) ->
        (((v₁ ≤ 64) = True)) ∧
        (∀ (v₂ : Int),
         (v₂ ≤ num_impl_5_BITS) ->
          (v₂ ≥ 0) ->
           (((v₂ ≤ 64) = True)) ∧
           (∀ (v₃ : Int),
            (v₃ ≤ num_impl_5_BITS) ->
             (v₃ ≥ 0) ->
              (((v₃ ≤ 64) = True)) ∧
              (∀ (v₄ : Int),
               (v₄ ≤ num_impl_5_BITS) ->
                (v₄ ≥ 0) ->
                 (((v₄ ≤ 64) = True)) ∧
                 (∀ (v₅ : Int),
                  (v₅ ≤ num_impl_5_BITS) ->
                   (v₅ ≥ 0) ->
                    ((v₅ ≤ 64) = True))
                 )
              )
           )
        )
     
end F
