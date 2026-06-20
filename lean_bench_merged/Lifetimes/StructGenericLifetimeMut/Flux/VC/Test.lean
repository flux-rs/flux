import Lifetimes.StructGenericLifetimeMut.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (((x₀ + 1) > 0)) ∧
   (∀ (v₀ : Int),
    (v₀ > 0) ->
     ((v₀ + 1) > 0))
   
end F
