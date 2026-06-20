import ExternSpecs.FluxCoreAlloc00.Flux.Prelude
import ExternSpecs.FluxCoreAlloc00.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestUncheckedFrom := 
 ((((4 + 4) - 1) ≤ num_impl_5_MAX)) ∧
 (((BitVec.and (BitVec.ofInt 64 4) (BitVec.sub (BitVec.ofInt 64 4) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0)))
 
end F
