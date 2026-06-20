import Surface.BoundedQuant00.Flux.Prelude
import Surface.BoundedQuant00.User.Fun.Magic
open Classical
set_option linter.unusedVariables false


namespace F



def TestAllR := 
 ∀ (n₀ : Int),
  (magic 0 n₀) ->
   (magic 1 n₀) ->
    (magic 2 n₀) ->
     (magic 3 n₀) ->
      ((((magic 0 n₀) ∧ (magic 1 n₀)) ∧ (magic 2 n₀)) ∧ (magic 3 n₀))
end F
