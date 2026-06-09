import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Pair
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> Prop, 
 ∀ (p₀ : Pair),
  ∀ (b₀ : Prop),
   ((¬b₀) ->
    ((k0 (Pair.a p₀) (Pair.b p₀) (Pair.a p₀) (Pair.b p₀) b₀))) ∧
   (b₀ ->
    ((k0 (Pair.a p₀) ((Pair.b p₀) + 1) (Pair.a p₀) (Pair.b p₀) True))) ∧
   (∀ (p₁ : Pair),
    ((k0 (Pair.a p₁) (Pair.b p₁) (Pair.a p₀) (Pair.b p₀) b₀)) ->
     ((Pair.a p₁) = (Pair.a p₀)))
   
end F
