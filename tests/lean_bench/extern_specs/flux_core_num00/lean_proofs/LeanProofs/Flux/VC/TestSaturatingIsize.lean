import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanProofs.Flux.Fun.Num{impl#5}MAX
import LeanFixpoint
open Classical

namespace F



def TestSaturatingIsize := 
 ((((if ((10 - 5) < num_{impl#5}_MIN) then num_{impl#5}_MIN else (if ((10 - 5) > num_{impl#5}_MAX) then num_{impl#5}_MAX else (10 - 5))) = 5) = True)) ∧
 ((((if ((((-9223372036854775808) + 5) - 10) < num_{impl#5}_MIN) then num_{impl#5}_MIN else (if ((((-9223372036854775808) + 5) - 10) > num_{impl#5}_MAX) then num_{impl#5}_MAX else (((-9223372036854775808) + 5) - 10))) = (-9223372036854775808)) = True)) ∧
 ((((if ((5 + 10) < num_{impl#5}_MIN) then num_{impl#5}_MIN else (if ((5 + 10) > num_{impl#5}_MAX) then num_{impl#5}_MAX else (5 + 10))) = 15) = True)) ∧
 ((((if (((9223372036854775807 - 5) + 10) < num_{impl#5}_MIN) then num_{impl#5}_MIN else (if (((9223372036854775807 - 5) + 10) > num_{impl#5}_MAX) then num_{impl#5}_MAX else ((9223372036854775807 - 5) + 10))) = 9223372036854775807) = True)) ∧
 ((((if ((((-9223372036854775808) + 5) + (-10)) < num_{impl#5}_MIN) then num_{impl#5}_MIN else (if ((((-9223372036854775808) + 5) + (-10)) > num_{impl#5}_MAX) then num_{impl#5}_MAX else (((-9223372036854775808) + 5) + (-10)))) = (-9223372036854775808)) = True))
 
end F
