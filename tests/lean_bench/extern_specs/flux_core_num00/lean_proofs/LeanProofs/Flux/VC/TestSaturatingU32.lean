import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestSaturatingU32 := 
 (((4294967295 - 5) ≥ 0)) ∧
 (((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_impl_8_MAX) then num_impl_8_MAX else (10 - 5))) ≥ 0) ->
  ((((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_impl_8_MAX) then num_impl_8_MAX else (10 - 5))) = 5) = True)) ∧
  (((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_impl_8_MAX) then num_impl_8_MAX else (5 - 10))) ≥ 0) ->
   ((((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_impl_8_MAX) then num_impl_8_MAX else (5 - 10))) = 0) = True)) ∧
   (((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_impl_8_MAX) then num_impl_8_MAX else (5 + 10))) ≥ 0) ->
    ((((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_impl_8_MAX) then num_impl_8_MAX else (5 + 10))) = 15) = True)) ∧
    (((if (((4294967295 - 5) + 10) < 0) then 0 else (if (((4294967295 - 5) + 10) > num_impl_8_MAX) then num_impl_8_MAX else ((4294967295 - 5) + 10))) ≥ 0) ->
     (((if (((4294967295 - 5) + 10) < 0) then 0 else (if (((4294967295 - 5) + 10) > num_impl_8_MAX) then num_impl_8_MAX else ((4294967295 - 5) + 10))) = 4294967295) = True))
    )
   )
  )
 
end F
