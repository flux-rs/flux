import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PairPair
open Classical
set_option linter.unusedVariables false


namespace F



def OpaqueStruct01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> Prop, 
 ∀ (p₀ : PairPair),
  ∀ (b₀ : Prop),
   ((¬b₀) ->
    ((k0 1 2 (PairPair.a p₀) (PairPair.b p₀) b₀))) ∧
   (b₀ ->
    ((k0 0 1 (PairPair.a p₀) (PairPair.b p₀) True))) ∧
   (∀ (p₁ : Int),
    ∀ (p₂ : Int),
     ((k0 p₁ p₂ (PairPair.a p₀) (PairPair.b p₀) b₀)) ->
      ((p₂ > p₁) = True))
   
end F
