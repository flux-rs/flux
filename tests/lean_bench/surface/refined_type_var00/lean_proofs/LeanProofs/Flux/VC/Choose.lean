import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Choose := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  ∀ (n₀ : Int),
   ∀ (m₀ : Int),
    ((¬b₀) ->
     ((k0 m₀ b₀ n₀ m₀))) ∧
    (b₀ ->
     ((k0 n₀ True n₀ m₀))) ∧
    (∀ (a'₀ : Int),
     ((k0 a'₀ b₀ n₀ m₀)) ->
      (a'₀ = (if b₀ then n₀ else m₀)))
    
end F
