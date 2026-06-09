import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Lib := 
 ∀ (constgen_N_0 : Int),
  ∀ (constgen_M_1 : Int),
   (constgen_M_1 ≥ 0) ->
    (constgen_M_1 > 10) ->
     (0 < constgen_M_1)
end F
