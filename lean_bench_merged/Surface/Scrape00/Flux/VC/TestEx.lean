import Surface.Scrape00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestEx := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≤ hi₀) ->
    (lo₀ ≥ 0) ->
     (hi₀ ≥ 0) ->
      (((k0 lo₀ 0 lo₀ hi₀))) ∧
      (∀ (i₀ : Int),
       ∀ (res₀ : Int),
        ((k0 i₀ res₀ lo₀ hi₀)) ->
         ((¬(i₀ < hi₀)) ->
          (res₀ = (hi₀ - lo₀))) ∧
         ((i₀ < hi₀) ->
          ((k0 (i₀ + 1) (res₀ + 1) lo₀ hi₀)))
         )
      
end F
