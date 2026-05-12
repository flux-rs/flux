import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__0__Test02 := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ ≤ 4294967295) ->
    (a'₀ ≠ 0) ->
     (((a'₀ - 1) ≥ 0)) ∧
     (((a'₀ - 1) ≤ 4294967295))
     
end F
