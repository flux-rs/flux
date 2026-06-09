import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Succ := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (((k0 n₀ n₀))) ∧
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀)) ->
     (0 ≤ a'₀) ->
      ((a'₀ + 1) = (n₀ + 1)))
   
end F
