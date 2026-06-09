import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  (a'₀ > 0) ->
   (((k0 (a'₀ - 1) a'₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ a'₀)) ->
     (a'₁ ≥ 0))
   
end F
