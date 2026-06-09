import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanProofs.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestSaturatingIsize := 
 ((((if ((10 - 5) < num_impl_5_MIN) then num_impl_5_MIN else (if ((10 - 5) > num_impl_5_MAX) then num_impl_5_MAX else (10 - 5))) = 5) = True)) ∧
 ((((if ((((-9223372036854775808) + 5) - 10) < num_impl_5_MIN) then num_impl_5_MIN else (if ((((-9223372036854775808) + 5) - 10) > num_impl_5_MAX) then num_impl_5_MAX else (((-9223372036854775808) + 5) - 10))) = (-9223372036854775808)) = True)) ∧
 ((((if ((5 + 10) < num_impl_5_MIN) then num_impl_5_MIN else (if ((5 + 10) > num_impl_5_MAX) then num_impl_5_MAX else (5 + 10))) = 15) = True)) ∧
 ((((if (((9223372036854775807 - 5) + 10) < num_impl_5_MIN) then num_impl_5_MIN else (if (((9223372036854775807 - 5) + 10) > num_impl_5_MAX) then num_impl_5_MAX else ((9223372036854775807 - 5) + 10))) = 9223372036854775807) = True)) ∧
 ((((if ((((-9223372036854775808) + 5) + (-10)) < num_impl_5_MIN) then num_impl_5_MIN else (if ((((-9223372036854775808) + 5) + (-10)) > num_impl_5_MAX) then num_impl_5_MAX else (((-9223372036854775808) + 5) + (-10)))) = (-9223372036854775808)) = True))
 
end F
