import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MAX
import LeanProofs.Flux.Fun.NumImpl2MIN
open Classical
set_option linter.unusedVariables false


namespace F



def TestWrappingI32 := 
 ((((if ((2147483647 + 1) > num_impl_2_MAX) then ((2147483647 + 1) - ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (if ((2147483647 + 1) < num_impl_2_MIN) then ((2147483647 + 1) + ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (2147483647 + 1))) = (-2147483648)) = True)) ∧
 ((((if (((-2147483648) - 1) > num_impl_2_MAX) then (((-2147483648) - 1) - ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (if (((-2147483648) - 1) < num_impl_2_MIN) then (((-2147483648) - 1) + ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else ((-2147483648) - 1))) = 2147483647) = True)) ∧
 ((((if ((10 + 5) > num_impl_2_MAX) then ((10 + 5) - ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (if ((10 + 5) < num_impl_2_MIN) then ((10 + 5) + ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (10 + 5))) = 15) = True)) ∧
 ((((if ((10 - 5) > num_impl_2_MAX) then ((10 - 5) - ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (if ((10 - 5) < num_impl_2_MIN) then ((10 - 5) + ((num_impl_2_MAX - num_impl_2_MIN) + 1)) else (10 - 5))) = 5) = True))
 
end F
