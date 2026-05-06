import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanFixpoint
open Classical

namespace F



def TestSaturatingI32 := 
 ((((if ((10 - 5) < num_{impl#2}_MIN) then num_{impl#2}_MIN else (if ((10 - 5) > num_{impl#2}_MAX) then num_{impl#2}_MAX else (10 - 5))) = 5) = True)) ∧
 ((((if ((((-2147483648) + 5) - 10) < num_{impl#2}_MIN) then num_{impl#2}_MIN else (if ((((-2147483648) + 5) - 10) > num_{impl#2}_MAX) then num_{impl#2}_MAX else (((-2147483648) + 5) - 10))) = (-2147483648)) = True)) ∧
 ((((if ((5 + 10) < num_{impl#2}_MIN) then num_{impl#2}_MIN else (if ((5 + 10) > num_{impl#2}_MAX) then num_{impl#2}_MAX else (5 + 10))) = 15) = True)) ∧
 ((((if (((2147483647 - 5) + 10) < num_{impl#2}_MIN) then num_{impl#2}_MIN else (if (((2147483647 - 5) + 10) > num_{impl#2}_MAX) then num_{impl#2}_MAX else ((2147483647 - 5) + 10))) = 2147483647) = True)) ∧
 ((((if ((((-2147483648) + 5) + (-10)) < num_{impl#2}_MIN) then num_{impl#2}_MIN else (if ((((-2147483648) + 5) + (-10)) > num_{impl#2}_MAX) then num_{impl#2}_MAX else (((-2147483648) + 5) + (-10)))) = (-2147483648)) = True))
 
end F
