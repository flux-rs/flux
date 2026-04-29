import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Foo
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (foo₀ : Foo),
  (0 ≤ (Foo.a foo₀)) ->
   ((Foo.a foo₀) < (Foo.b foo₀)) ->
    ((0 < (Foo.b foo₀)) = True)
end F
