import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl11MAX
import LeanFixpoint
open Classical

namespace F



def TestSaturatingUsize := 
 (((18446744073709551615 - 5) ≥ 0)) ∧
 (((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_impl_11_MAX) then num_impl_11_MAX else (10 - 5))) ≥ 0) ->
  ((((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_impl_11_MAX) then num_impl_11_MAX else (10 - 5))) = 5) = True)) ∧
  (((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_impl_11_MAX) then num_impl_11_MAX else (5 - 10))) ≥ 0) ->
   ((((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_impl_11_MAX) then num_impl_11_MAX else (5 - 10))) = 0) = True)) ∧
   (((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_impl_11_MAX) then num_impl_11_MAX else (5 + 10))) ≥ 0) ->
    ((((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_impl_11_MAX) then num_impl_11_MAX else (5 + 10))) = 15) = True)) ∧
    (((if (((18446744073709551615 - 5) + 10) < 0) then 0 else (if (((18446744073709551615 - 5) + 10) > num_impl_11_MAX) then num_impl_11_MAX else ((18446744073709551615 - 5) + 10))) ≥ 0) ->
     (((if (((18446744073709551615 - 5) + 10) < 0) then 0 else (if (((18446744073709551615 - 5) + 10) > num_impl_11_MAX) then num_impl_11_MAX else ((18446744073709551615 - 5) + 10))) = 18446744073709551615) = True))
    )
   )
  )
 
end F
