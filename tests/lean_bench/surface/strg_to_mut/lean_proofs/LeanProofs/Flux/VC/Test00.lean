import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (v₀ ≥ 0) ->
   (((k0 (v₀ + 1) v₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ v₀)) ->
     ((a'₁ > 0)) ∧
     (∀ (v₁ : Int),
      (v₁ > 0) ->
       ((k0 (v₁ + 1) v₀)))
     )
   
end F
