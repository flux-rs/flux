import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FibLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (0 < v₀) ->
   (((k0 v₀ 1 1 v₀))) ∧
   (∀ (k₀ : Int),
    ∀ (i₀ : Int),
     ∀ (j₀ : Int),
      ((k0 k₀ i₀ j₀ v₀)) ->
       ((¬(k₀ > 2)) ->
        (0 < i₀)) ∧
       ((k₀ > 2) ->
        ((k0 (k₀ - 1) (i₀ + j₀) i₀ v₀)))
       )
   
end F
