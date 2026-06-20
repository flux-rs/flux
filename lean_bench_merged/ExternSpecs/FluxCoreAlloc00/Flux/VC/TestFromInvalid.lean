import ExternSpecs.FluxCoreAlloc00.Flux.Prelude
import ExternSpecs.FluxCoreAlloc00.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestFromInvalid := 
 (((¬((((0 + 3) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 3) (BitVec.sub (BitVec.ofInt 64 3) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0)))) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 9223372036854775807)) ->
    (((a'₀ - 2) ≥ 0)) ∧
    (((¬(((((a'₀ - 2) + 3) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 3) (BitVec.sub (BitVec.ofInt 64 3) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0)))) = True))
    )
 
end F
