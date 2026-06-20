import ExternSpecs.FluxCoreAlloc00.Flux.Prelude
import ExternSpecs.FluxCoreAlloc00.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestArray := 
 (((False ∨ ((((4 * 10) + 4) - 1) ≤ num_impl_5_MAX)) = True)) ∧
 (((False ∨ ((((4 * 12) + 4) - 1) ≤ num_impl_5_MAX)) = True)) ∧
 (((¬(False ∨ ((((8 * 18446744073709551615) + 8) - 1) ≤ num_impl_5_MAX))) = True))
 
end F
