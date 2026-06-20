import Surface.RefinedFnInTrait01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 42))) ∧
 (∀ (v₀ : Int),
  ((k0 v₀)) ->
   (((v₀ = 42) = True)) ∧
   (((k1 42 v₀))) ∧
   (∀ (v₁ : Int),
    ((k1 v₁ v₀)) ->
     ((v₁ = 42) = True))
   )
 
end F
