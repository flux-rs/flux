import Surface.TryFrom00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar := 
 ∀ (my_num₀ : Int),
  (42 = my_num₀) ->
   ((my_num₀ = 42) = True)
end F
