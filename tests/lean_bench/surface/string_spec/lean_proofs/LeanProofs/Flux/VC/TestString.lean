import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestString := 
 ((("bob" = "bob") = True)) ∧
 ((("bob" = "bob") = True)) ∧
 ((("alice" = "alice") = True)) ∧
 (∀ (v₀ : Prop),
  (v₀ <-> True) ->
   ((v₀ = True)) ∧
   (∀ (v₁ : Prop),
    (v₁ <-> True) ->
     (v₁ = True))
   )
 
end F
