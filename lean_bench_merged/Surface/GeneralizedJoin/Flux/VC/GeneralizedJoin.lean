import Surface.GeneralizedJoin.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def GeneralizedJoin := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 0 0 n₀))) ∧
  (∀ (i₀ : Int),
   ∀ (j₀ : Int),
    ((k0 i₀ j₀ n₀)) ->
     ((¬(i₀ < n₀)) ->
      ((i₀ - j₀) = 0)) ∧
     ((i₀ < n₀) ->
      ((k0 (i₀ + 1) (j₀ + 1) n₀)))
     )
  
end F
