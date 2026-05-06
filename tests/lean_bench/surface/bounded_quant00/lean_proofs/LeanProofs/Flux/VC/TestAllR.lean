import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.Magic
import LeanFixpoint
open Classical

namespace F



def TestAllR := 
 ∀ (n₀ : Int),
  (magic 0 n₀) ->
   (magic 1 n₀) ->
    (magic 2 n₀) ->
     (magic 3 n₀) ->
      ((((magic 0 n₀) ∧ (magic 1 n₀)) ∧ (magic 2 n₀)) ∧ (magic 3 n₀))
end F
