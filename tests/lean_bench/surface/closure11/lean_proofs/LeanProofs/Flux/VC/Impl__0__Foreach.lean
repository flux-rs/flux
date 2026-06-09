import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__Foreach := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (0 ≤ n₀) ->
     (n₀ ≥ 0) ->
      (∀ (a'₁ : Int),
       ((k0 a'₁ n₀ f₀)) ->
        (a'₁ ≥ 0) ->
         False ->
          ((c0) ∨ False)) ∧
      (∀ (item₀ : Int),
       ((0 ≤ item₀) ∧ (item₀ < n₀)) ->
        ((k0 item₀ n₀ f₀)))
      
end F
