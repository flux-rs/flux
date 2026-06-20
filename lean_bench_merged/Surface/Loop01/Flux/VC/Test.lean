import Surface.Loop01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 0 0))) ∧
 (∀ (i₀ : Int),
  ∀ (res₀ : Int),
   ((k0 i₀ res₀)) ->
    ((¬(i₀ < 100)) ->
     (0 ≤ res₀)) ∧
    ((i₀ < 100) ->
     ((k0 (i₀ + 1) (res₀ + 1))))
    )
 
end F
