import Surface.CheckOverflow02.Flux.Prelude
import Surface.CheckOverflow02.Flux.Fun.MAX
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__Add2 := 
 ∀ (inner₀ : Int),
  ((inner₀ + 2) ≤ MAX) ->
   (inner₀ ≥ 0) ->
    (inner₀ ≤ 4294967295) ->
     (((inner₀ + 2) ≥ 0)) ∧
     (((inner₀ + 2) ≤ 4294967295))
     
end F
