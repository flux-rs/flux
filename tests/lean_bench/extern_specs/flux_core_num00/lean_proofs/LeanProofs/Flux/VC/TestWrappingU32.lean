import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}MAX
import LeanFixpoint
open Classical

namespace F



def TestWrappingU32 := 
 ((if ((4294967295 + 1) > num_{impl#8}_MAX) then ((4294967295 + 1) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((4294967295 + 1) < 0) then ((4294967295 + 1) + ((num_{impl#8}_MAX - 0) + 1)) else (4294967295 + 1))) ≥ 0) ->
  ((((if ((4294967295 + 1) > num_{impl#8}_MAX) then ((4294967295 + 1) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((4294967295 + 1) < 0) then ((4294967295 + 1) + ((num_{impl#8}_MAX - 0) + 1)) else (4294967295 + 1))) = 0) = True)) ∧
  (((if ((0 - 1) > num_{impl#8}_MAX) then ((0 - 1) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((0 - 1) < 0) then ((0 - 1) + ((num_{impl#8}_MAX - 0) + 1)) else (0 - 1))) ≥ 0) ->
   ((((if ((0 - 1) > num_{impl#8}_MAX) then ((0 - 1) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((0 - 1) < 0) then ((0 - 1) + ((num_{impl#8}_MAX - 0) + 1)) else (0 - 1))) = 4294967295) = True)) ∧
   (((if ((10 + 5) > num_{impl#8}_MAX) then ((10 + 5) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((10 + 5) < 0) then ((10 + 5) + ((num_{impl#8}_MAX - 0) + 1)) else (10 + 5))) ≥ 0) ->
    ((((if ((10 + 5) > num_{impl#8}_MAX) then ((10 + 5) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((10 + 5) < 0) then ((10 + 5) + ((num_{impl#8}_MAX - 0) + 1)) else (10 + 5))) = 15) = True)) ∧
    (((if ((10 - 5) > num_{impl#8}_MAX) then ((10 - 5) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((10 - 5) < 0) then ((10 - 5) + ((num_{impl#8}_MAX - 0) + 1)) else (10 - 5))) ≥ 0) ->
     (((if ((10 - 5) > num_{impl#8}_MAX) then ((10 - 5) - ((num_{impl#8}_MAX - 0) + 1)) else (if ((10 - 5) < 0) then ((10 - 5) + ((num_{impl#8}_MAX - 0) + 1)) else (10 - 5))) = 5) = True))
    )
   )
  
end F
