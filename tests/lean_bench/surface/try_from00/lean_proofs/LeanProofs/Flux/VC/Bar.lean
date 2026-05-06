import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Bar := 
 ∀ (my_num₀ : Int),
  (42 = my_num₀) ->
   ((my_num₀ = 42) = True)
end F
