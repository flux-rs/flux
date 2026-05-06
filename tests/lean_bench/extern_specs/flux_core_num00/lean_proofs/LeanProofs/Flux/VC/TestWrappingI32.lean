import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanFixpoint
open Classical

namespace F



def TestWrappingI32 := 
 ((((if ((2147483647 + 1) > num_{impl#2}_MAX) then ((2147483647 + 1) - ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (if ((2147483647 + 1) < num_{impl#2}_MIN) then ((2147483647 + 1) + ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (2147483647 + 1))) = (-2147483648)) = True)) ∧
 ((((if (((-2147483648) - 1) > num_{impl#2}_MAX) then (((-2147483648) - 1) - ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (if (((-2147483648) - 1) < num_{impl#2}_MIN) then (((-2147483648) - 1) + ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else ((-2147483648) - 1))) = 2147483647) = True)) ∧
 ((((if ((10 + 5) > num_{impl#2}_MAX) then ((10 + 5) - ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (if ((10 + 5) < num_{impl#2}_MIN) then ((10 + 5) + ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (10 + 5))) = 15) = True)) ∧
 ((((if ((10 - 5) > num_{impl#2}_MAX) then ((10 - 5) - ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (if ((10 - 5) < num_{impl#2}_MIN) then ((10 - 5) + ((num_{impl#2}_MAX - num_{impl#2}_MIN) + 1)) else (10 - 5))) = 5) = True))
 
end F
