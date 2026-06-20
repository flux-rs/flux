import Surface.Primops00.Flux.Prelude
import Surface.Primops00.Flux.Const.PrimOpBitAndInt
open Classical
set_option linter.unusedVariables false


namespace F



def Test7 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   ((k0 6 b₀))) ∧
  (b₀ ->
   ((PrimOpBitAndInt 10 7) ≤ 7) ->
    ((k0 (PrimOpBitAndInt 10 7) True))) ∧
  (∀ (m₀ : Int),
   ((k0 m₀ b₀)) ->
    (m₀ ≤ 7))
  
end F
