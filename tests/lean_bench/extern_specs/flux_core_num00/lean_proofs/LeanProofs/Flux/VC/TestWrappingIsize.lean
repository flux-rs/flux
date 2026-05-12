import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanFixpoint
open Classical

namespace F



def TestWrappingIsize := 
 ((((if ((9223372036854775807 + 1) > num_impl_5_MAX) then ((9223372036854775807 + 1) - ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (if ((9223372036854775807 + 1) < num_impl_5_MIN) then ((9223372036854775807 + 1) + ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (9223372036854775807 + 1))) = (-9223372036854775808)) = True)) ∧
 ((((if (((-9223372036854775808) - 1) > num_impl_5_MAX) then (((-9223372036854775808) - 1) - ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (if (((-9223372036854775808) - 1) < num_impl_5_MIN) then (((-9223372036854775808) - 1) + ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else ((-9223372036854775808) - 1))) = 9223372036854775807) = True)) ∧
 ((((if ((10 + 5) > num_impl_5_MAX) then ((10 + 5) - ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (if ((10 + 5) < num_impl_5_MIN) then ((10 + 5) + ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (10 + 5))) = 15) = True)) ∧
 ((((if ((10 - 5) > num_impl_5_MAX) then ((10 - 5) - ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (if ((10 - 5) < num_impl_5_MIN) then ((10 - 5) + ((num_impl_5_MAX - num_impl_5_MIN) + 1)) else (10 - 5))) = 5) = True))
 
end F
