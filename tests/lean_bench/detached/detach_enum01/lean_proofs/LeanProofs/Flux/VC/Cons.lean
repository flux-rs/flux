import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Cons := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (h₀ : Int),
   (n₀ ≥ 0) ->
    (((k0 n₀ n₀ h₀))) ∧
    (∀ (a'₁ : Int),
     ((k0 a'₁ n₀ h₀)) ->
      (a'₁ ≥ 0) ->
       ((a'₁ + 1) = (n₀ + 1)))
    
end F
