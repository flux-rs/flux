import Structs.Dot01.Flux.Prelude
import Structs.Dot01.Flux.Struct.Pair
open Classical
set_option linter.unusedVariables false


namespace F



def MkPairsWithBound := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (a₀ : Int),
  (((k0 0 0 a₀))) ∧
  (∀ (i₀ : Int),
   ∀ (res₀ : Int),
    ((k0 i₀ res₀ a₀)) ->
     ((¬(i₀ < a₀)) ->
      ∀ (a'₂ : Pair),
       ((k1 (Pair.x a'₂) (Pair.y a'₂) i₀ res₀ a₀)) ->
        (((Pair.x a'₂) + (Pair.y a'₂)) ≤ a₀)) ∧
     ((i₀ < a₀) ->
      (∀ (a'₃ : Pair),
       ((k1 (Pair.x a'₃) (Pair.y a'₃) i₀ res₀ a₀)) ->
        ((k2 (Pair.x a'₃) (Pair.y a'₃) a₀ i₀ res₀))) ∧
      (((k2 i₀ (a₀ - i₀) a₀ i₀ res₀))) ∧
      ((0 ≤ (res₀ + 1)) ->
       (((k0 (i₀ + 1) (res₀ + 1) a₀))) ∧
       (∀ (a'₄ : Pair),
        ((k2 (Pair.x a'₄) (Pair.y a'₄) a₀ i₀ res₀)) ->
         ((k1 (Pair.x a'₄) (Pair.y a'₄) (i₀ + 1) (res₀ + 1) a₀)))
       )
      )
     )
  
end F
