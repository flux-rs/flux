import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Mod33
import LeanProofs.Flux.Fun.Foo
open Classical
set_option linter.unusedVariables false


namespace F



def UseFoo := 
 ∀ (n₀ : Int),
  (¬(n₀ ≠ 40)) ->
   (foo n₀ 7)
end F
