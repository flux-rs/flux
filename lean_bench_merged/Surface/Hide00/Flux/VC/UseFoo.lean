import Surface.Hide00.Flux.Prelude
import Surface.Hide00.Flux.Fun.Mod33
import Surface.Hide00.Flux.Fun.Foo
open Classical
set_option linter.unusedVariables false


namespace F



def UseFoo := 
 ∀ (n₀ : Int),
  (¬(n₀ ≠ 40)) ->
   (foo n₀ 7)
end F
