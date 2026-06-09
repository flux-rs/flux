import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestRc := ∃ k0 : (a0 : String) -> Prop, ∃ k1 : (a0 : String) -> Prop, 
 (((k0 "bob"))) ∧
 (∀ (a'₀ : String),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (((k1 "bob")) ->
  (("bob" = "bob") = True))
 
end F
