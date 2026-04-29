import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#11}MAX
import LeanFixpoint
open Classical

namespace F



def TestWrappingUsize := 
 ((if ((18446744073709551615 + 1) > num_{impl#11}_MAX) then ((18446744073709551615 + 1) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((18446744073709551615 + 1) < 0) then ((18446744073709551615 + 1) + ((num_{impl#11}_MAX - 0) + 1)) else (18446744073709551615 + 1))) ≥ 0) ->
  ((((if ((18446744073709551615 + 1) > num_{impl#11}_MAX) then ((18446744073709551615 + 1) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((18446744073709551615 + 1) < 0) then ((18446744073709551615 + 1) + ((num_{impl#11}_MAX - 0) + 1)) else (18446744073709551615 + 1))) = 0) = True)) ∧
  (((if ((0 - 1) > num_{impl#11}_MAX) then ((0 - 1) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((0 - 1) < 0) then ((0 - 1) + ((num_{impl#11}_MAX - 0) + 1)) else (0 - 1))) ≥ 0) ->
   ((((if ((0 - 1) > num_{impl#11}_MAX) then ((0 - 1) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((0 - 1) < 0) then ((0 - 1) + ((num_{impl#11}_MAX - 0) + 1)) else (0 - 1))) = 18446744073709551615) = True)) ∧
   (((if ((10 + 5) > num_{impl#11}_MAX) then ((10 + 5) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((10 + 5) < 0) then ((10 + 5) + ((num_{impl#11}_MAX - 0) + 1)) else (10 + 5))) ≥ 0) ->
    ((((if ((10 + 5) > num_{impl#11}_MAX) then ((10 + 5) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((10 + 5) < 0) then ((10 + 5) + ((num_{impl#11}_MAX - 0) + 1)) else (10 + 5))) = 15) = True)) ∧
    (((if ((10 - 5) > num_{impl#11}_MAX) then ((10 - 5) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((10 - 5) < 0) then ((10 - 5) + ((num_{impl#11}_MAX - 0) + 1)) else (10 - 5))) ≥ 0) ->
     (((if ((10 - 5) > num_{impl#11}_MAX) then ((10 - 5) - ((num_{impl#11}_MAX - 0) + 1)) else (if ((10 - 5) < 0) then ((10 - 5) + ((num_{impl#11}_MAX - 0) + 1)) else (10 - 5))) = 5) = True))
    )
   )
  
end F
