import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (((k0 (a'₀ + 1)))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁)) ->
     ∀ (a'₂ : Int),
      ((k0 a'₂)) ->
       (a'₁ ≥ 0))
   )
 
end F
