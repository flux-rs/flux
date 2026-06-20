import Enums.List00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Clone := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (val₀ : Int),
   (n₀ ≥ 0) ->
    ((n₀ ≠ 0) ->
     (((n₀ - 1) ≥ 0)) ∧
     (((n₀ - 1) ≥ 0) ->
      (((k0 (n₀ - 1) n₀ val₀))) ∧
      (∀ (a'₁ : Int),
       ((k0 a'₁ n₀ val₀)) ->
        (a'₁ ≥ 0) ->
         ((a'₁ + 1) = n₀))
      )
     ) ∧
    ((¬(n₀ ≠ 0)) ->
     (0 = n₀))
    
end F
