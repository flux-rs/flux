import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}MAX
import LeanFixpoint
open Classical

namespace F



def TestSaturatingU32 := 
 (((4294967295 - 5) ≥ 0)) ∧
 (((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (10 - 5))) ≥ 0) ->
  ((((if ((10 - 5) < 0) then 0 else (if ((10 - 5) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (10 - 5))) = 5) = True)) ∧
  (((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (5 - 10))) ≥ 0) ->
   ((((if ((5 - 10) < 0) then 0 else (if ((5 - 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (5 - 10))) = 0) = True)) ∧
   (((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (5 + 10))) ≥ 0) ->
    ((((if ((5 + 10) < 0) then 0 else (if ((5 + 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else (5 + 10))) = 15) = True)) ∧
    (((if (((4294967295 - 5) + 10) < 0) then 0 else (if (((4294967295 - 5) + 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else ((4294967295 - 5) + 10))) ≥ 0) ->
     (((if (((4294967295 - 5) + 10) < 0) then 0 else (if (((4294967295 - 5) + 10) > num_{impl#8}_MAX) then num_{impl#8}_MAX else ((4294967295 - 5) + 10))) = 4294967295) = True))
    )
   )
  )
 
end F
