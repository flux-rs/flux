import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 (32000 = (let a'₀ := (10 * 2); (let a'₁ := (a'₀ * 2); ((a'₁ * a'₁) * a'₀))))
end F
