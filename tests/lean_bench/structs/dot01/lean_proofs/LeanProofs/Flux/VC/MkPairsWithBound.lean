import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Pair
import LeanFixpoint
open Classical

namespace F



def MkPairsWithBound := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (a₀ : Int),
  (((k0 0 0 a₀))) ∧
  (∀ (res₀ : Int),
   ∀ (i₀ : Int),
    ((k0 res₀ i₀ a₀)) ->
     ((¬(i₀ < a₀)) ->
      ∀ (a'₂ : Pair),
       ((k1 (Pair.x a'₂) (Pair.y a'₂) res₀ i₀ a₀)) ->
        (((Pair.x a'₂) + (Pair.y a'₂)) ≤ a₀)) ∧
     ((i₀ < a₀) ->
      (∀ (a'₃ : Pair),
       ((k1 (Pair.x a'₃) (Pair.y a'₃) res₀ i₀ a₀)) ->
        ((k2 (Pair.x a'₃) (Pair.y a'₃) a₀ res₀ i₀))) ∧
      (((k2 i₀ (a₀ - i₀) a₀ res₀ i₀))) ∧
      ((0 ≤ (res₀ + 1)) ->
       (((k0 (res₀ + 1) (i₀ + 1) a₀))) ∧
       (∀ (a'₄ : Pair),
        ((k2 (Pair.x a'₄) (Pair.y a'₄) a₀ res₀ i₀)) ->
         ((k1 (Pair.x a'₄) (Pair.y a'₄) (res₀ + 1) (i₀ + 1) a₀)))
       )
      )
     )
  
end F
