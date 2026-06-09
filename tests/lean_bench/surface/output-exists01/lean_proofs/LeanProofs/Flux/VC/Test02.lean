import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 n₀ n₀ n₀))) ∧
  (∀ (a'₀ : Int),
   ∀ (a'₁ : Int),
    ((k0 a'₀ a'₁ n₀)) ->
     ∀ (a'₂ : Prop),
      ((¬a'₂) ->
       (a'₁ = a'₀)) ∧
      (a'₂ ->
       ((k0 (a'₀ + 1) (a'₁ + 1) n₀)))
      )
  
end F
