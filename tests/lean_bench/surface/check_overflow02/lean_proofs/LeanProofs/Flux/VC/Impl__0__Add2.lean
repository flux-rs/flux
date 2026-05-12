import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.MAX
import LeanFixpoint
open Classical

namespace F



def Impl__0__Add2 := 
 ∀ (inner₀ : Int),
  ((inner₀ + 2) ≤ MAX) ->
   (inner₀ ≥ 0) ->
    (inner₀ ≤ 4294967295) ->
     (((inner₀ + 2) ≥ 0)) ∧
     (((inner₀ + 2) ≤ 4294967295))
     
end F
