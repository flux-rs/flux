import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 n₀ n₀))) ∧
   (∀ (res₀ : Int),
    ∀ (i₀ : Int),
     ((k0 res₀ i₀ n₀)) ->
      ((¬(i₀ > 0)) ->
       (res₀ = n₀)) ∧
      ((i₀ > 0) ->
       (((res₀ + i₀) ≠ n₀) ->
        ((k1 n₀ res₀ i₀))) ∧
       ((¬((res₀ + i₀) ≠ n₀)) ->
        (((99 - 99) ≥ 0)) ∧
        ((¬(i₀ ≥ (99 - 99))) ->
         ((k1 n₀ res₀ i₀))) ∧
        ((i₀ ≥ (99 - 99)) ->
         (((66 - 66) ≥ 0)) ∧
         (((k2 (res₀ ≥ (66 - 66)) n₀ res₀ i₀)))
         )
        ) ∧
       (((k1 n₀ res₀ i₀)) ->
        ((k2 False n₀ res₀ i₀))) ∧
       (∀ (a'₂ : Prop),
        ((k2 a'₂ n₀ res₀ i₀)) ->
         ((a'₂ = True)) ∧
         (((i₀ - 1) ≥ 0)) ∧
         (((k0 (res₀ + 1) (i₀ - 1) n₀)))
         )
       )
      )
   
end F
