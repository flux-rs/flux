import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__Get := 
 ∀ (constgen_N_0 : Int),
  ∀ (constgen_M_1 : Int),
   ∀ (i₀ : Int),
    ∀ (j₀ : Int),
     (i₀ < constgen_N_0) ->
      (j₀ < constgen_M_1) ->
       (i₀ ≥ 0) ->
        (j₀ ≥ 0) ->
         (0 ≤ (constgen_N_0 * constgen_M_1)) ->
          (((i₀ * constgen_M_1) + j₀) < (constgen_N_0 * constgen_M_1))
end F
