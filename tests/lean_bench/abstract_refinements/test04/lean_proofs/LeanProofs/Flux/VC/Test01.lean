import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (v₀ : Int),
  ((k0 v₀)) ->
   (((k1 (v₀ + 1) v₀))) ∧
   (∀ (a'₁ : Int),
    (((k1 a'₁ v₀)) ->
     (a'₁ ≥ 0)) ∧
    ((a'₁ ≥ 0) ->
     ((k1 a'₁ v₀)))
    )
   )
 
end F
