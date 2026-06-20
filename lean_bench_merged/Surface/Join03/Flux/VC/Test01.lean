import Surface.Join03.Flux.Prelude
import Surface.Join03.Flux.Struct.Pair
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (p₀ : Pair),
  (((k0 (Pair.a p₀) (Pair.b p₀) 0 (Pair.a p₀) (Pair.b p₀)))) ∧
  (∀ (p₁ : Pair),
   ∀ (i₀ : Int),
    ((k0 (Pair.a p₁) (Pair.b p₁) i₀ (Pair.a p₀) (Pair.b p₀))) ->
     ((¬(i₀ < 10)) ->
      ((Pair.a p₁) = (Pair.a p₀))) ∧
     ((i₀ < 10) ->
      ((k0 (Pair.a p₁) ((Pair.b p₁) + 1) (i₀ + 1) (Pair.a p₀) (Pair.b p₀))))
     )
  
end F
