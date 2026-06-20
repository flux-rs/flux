import ConstGenerics.StructInvariant.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Foo := 
 ∀ (constgen_N_0 : Int),
  ∀ (x₀ : Int),
   (x₀ ≥ 0) ->
    (constgen_N_0 > 0) ->
     (constgen_N_0 ≠ 0)
end F
