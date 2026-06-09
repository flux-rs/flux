import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  ∀ (s₀ : Int),
   ((¬b₀) ->
    (s₀ ≥ 0) ->
     ∀ (a'₂ : Int),
      ((k0 s₀ a'₂ b₀ s₀))) ∧
   (b₀ ->
    (s₀ ≥ 0) ->
     ∀ (a'₃ : Int),
      ((k0 (s₀ - 1) a'₃ True s₀))) ∧
   (∀ (s₁ : Int),
    ∀ (s₂ : Int),
     ((k0 s₁ s₂ b₀ s₀)) ->
      ((s₁ + 1) ≥ 0))
   
end F
