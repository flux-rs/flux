import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.Foo
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 n₀ n₀))) ∧
   (∀ (i₀ : Int),
    ((k0 i₀ n₀)) ->
     ((¬(i₀ < 5)) ->
      (i₀ ≥ 5)) ∧
     ((i₀ < 5) ->
      ((k0 (i₀ + 1) n₀)))
     )
   
end F
