import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__Foo := 
 ∀ (m₀ : Int),
  (m₀ < (m₀ + 1))
end F
