import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MAX
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanFixpoint
open Classical

namespace F



def TestWrappingIsize := 
 ((((if ((9223372036854775807 + 1) > num_{impl#5}_MAX) then ((9223372036854775807 + 1) - ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (if ((9223372036854775807 + 1) < num_{impl#5}_MIN) then ((9223372036854775807 + 1) + ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (9223372036854775807 + 1))) = (-9223372036854775808)) = True)) ∧
 ((((if (((-9223372036854775808) - 1) > num_{impl#5}_MAX) then (((-9223372036854775808) - 1) - ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (if (((-9223372036854775808) - 1) < num_{impl#5}_MIN) then (((-9223372036854775808) - 1) + ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else ((-9223372036854775808) - 1))) = 9223372036854775807) = True)) ∧
 ((((if ((10 + 5) > num_{impl#5}_MAX) then ((10 + 5) - ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (if ((10 + 5) < num_{impl#5}_MIN) then ((10 + 5) + ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (10 + 5))) = 15) = True)) ∧
 ((((if ((10 - 5) > num_{impl#5}_MAX) then ((10 - 5) - ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (if ((10 - 5) < num_{impl#5}_MIN) then ((10 - 5) + ((num_{impl#5}_MAX - num_{impl#5}_MIN) + 1)) else (10 - 5))) = 5) = True))
 
end F
