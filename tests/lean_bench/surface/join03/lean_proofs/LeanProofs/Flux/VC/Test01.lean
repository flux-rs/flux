import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Pair
import LeanFixpoint
open Classical

namespace F



def Test01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (p₀ : Pair),
  (((k0 0 (Pair.a p₀) (Pair.b p₀) (Pair.a p₀) (Pair.b p₀)))) ∧
  (∀ (i₀ : Int),
   ∀ (p₁ : Pair),
    ((k0 i₀ (Pair.a p₁) (Pair.b p₁) (Pair.a p₀) (Pair.b p₀))) ->
     ((¬(i₀ < 10)) ->
      ((Pair.a p₁) = (Pair.a p₀))) ∧
     ((i₀ < 10) ->
      ((k0 (i₀ + 1) (Pair.a p₁) ((Pair.b p₁) + 1) (Pair.a p₀) (Pair.b p₀))))
     )
  
end F
