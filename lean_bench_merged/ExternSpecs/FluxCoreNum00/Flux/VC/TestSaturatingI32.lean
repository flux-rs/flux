import ExternSpecs.FluxCoreNum00.Flux.Prelude
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MIN
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestSaturatingI32 := 
 ((((if ((10 - 5) < num_impl_2_MIN) then num_impl_2_MIN else (if ((10 - 5) > num_impl_2_MAX) then num_impl_2_MAX else (10 - 5))) = 5) = True)) ∧
 ((((if ((((-2147483648) + 5) - 10) < num_impl_2_MIN) then num_impl_2_MIN else (if ((((-2147483648) + 5) - 10) > num_impl_2_MAX) then num_impl_2_MAX else (((-2147483648) + 5) - 10))) = (-2147483648)) = True)) ∧
 ((((if ((5 + 10) < num_impl_2_MIN) then num_impl_2_MIN else (if ((5 + 10) > num_impl_2_MAX) then num_impl_2_MAX else (5 + 10))) = 15) = True)) ∧
 ((((if (((2147483647 - 5) + 10) < num_impl_2_MIN) then num_impl_2_MIN else (if (((2147483647 - 5) + 10) > num_impl_2_MAX) then num_impl_2_MAX else ((2147483647 - 5) + 10))) = 2147483647) = True)) ∧
 ((((if ((((-2147483648) + 5) + (-10)) < num_impl_2_MIN) then num_impl_2_MIN else (if ((((-2147483648) + 5) + (-10)) > num_impl_2_MAX) then num_impl_2_MAX else (((-2147483648) + 5) + (-10)))) = (-2147483648)) = True))
 
end F
