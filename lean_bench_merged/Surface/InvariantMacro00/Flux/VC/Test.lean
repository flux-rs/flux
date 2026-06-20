import Surface.InvariantMacro00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 n₀ 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (res₀ : Int),
     ((k0 i₀ res₀ n₀)) ->
      ((¬(i₀ > 0)) ->
       (res₀ = n₀)) ∧
      ((i₀ > 0) ->
       (((res₀ + i₀) ≠ n₀) ->
        ((k1 n₀ i₀ res₀))) ∧
       ((¬((res₀ + i₀) ≠ n₀)) ->
        (((99 - 99) ≥ 0)) ∧
        ((¬(i₀ ≥ (99 - 99))) ->
         ((k1 n₀ i₀ res₀))) ∧
        ((i₀ ≥ (99 - 99)) ->
         (((66 - 66) ≥ 0)) ∧
         (((k2 (res₀ ≥ (66 - 66)) n₀ i₀ res₀)))
         )
        ) ∧
       (((k1 n₀ i₀ res₀)) ->
        ((k2 False n₀ i₀ res₀))) ∧
       (∀ (a'₂ : Prop),
        ((k2 a'₂ n₀ i₀ res₀)) ->
         ((a'₂ = True)) ∧
         (((i₀ - 1) ≥ 0)) ∧
         (((k0 (i₀ - 1) (res₀ + 1) n₀)))
         )
       )
      )
   
end F
