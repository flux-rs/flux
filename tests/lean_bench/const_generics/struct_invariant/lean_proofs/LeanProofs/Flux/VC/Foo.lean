import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Foo := 
 ∀ (constgen_N_0 : Int),
  ∀ (x₀ : Int),
   (x₀ ≥ 0) ->
    (constgen_N_0 > 0) ->
     (constgen_N_0 ≠ 0)
end F
