import Surface.InvariantMacro00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestWithQualifier := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 n₀ 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (res₀ : Int),
     ((k0 i₀ res₀ n₀)) ->
      ((¬(i₀ > 0)) ->
       (res₀ = n₀)) ∧
      ((i₀ > 0) ->
       (((i₀ - 1) ≥ 0)) ∧
       (((k0 (i₀ - 1) (res₀ + 1) n₀)))
       )
      )
   
end F
