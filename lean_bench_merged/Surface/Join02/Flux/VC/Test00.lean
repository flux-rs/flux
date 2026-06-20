import Surface.Join02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   ((k0 1 b₀))) ∧
  (b₀ ->
   ((k0 0 True))) ∧
  (∀ (p₀ : Int),
   ((k0 p₀ b₀)) ->
    ((0 + p₀) ≥ 0))
  
end F
