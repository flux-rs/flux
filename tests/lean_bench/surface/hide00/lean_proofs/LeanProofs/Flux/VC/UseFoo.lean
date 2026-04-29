import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Mod33
import LeanProofs.Flux.Fun.Foo
import LeanFixpoint
open Classical

namespace F



def UseFoo := 
 ∀ (n₀ : Int),
  (¬(n₀ ≠ 40)) ->
   (foo n₀ 7)
end F
