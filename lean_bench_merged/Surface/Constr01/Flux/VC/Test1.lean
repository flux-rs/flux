import Surface.Constr01.Flux.Prelude
import Surface.Constr01.Flux.Struct.Foo
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ∀ (foo₀ : Foo),
  (0 ≤ (Foo.a foo₀)) ->
   ((Foo.a foo₀) < (Foo.b foo₀)) ->
    ((0 < (Foo.b foo₀)) = True)
end F
