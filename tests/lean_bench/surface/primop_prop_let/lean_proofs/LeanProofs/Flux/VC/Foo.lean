import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Foo := 
 (let a'₀ := 2; (let a'₁ := 4; ((c0 1 a'₀) = (a'₁ * 1)))) ->
  ((c0 1 2) = 4)
end F
