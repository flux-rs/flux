import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BazCall := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   ((k0 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((k1 (a'₁ + 1) a'₁))) ∧
   (∀ (a'₂ : Int),
    ((k1 a'₂ a'₁)) ->
     (a'₂ = 1))
   )
 
end F
