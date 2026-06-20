import Surface.Binop.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def LogicalOr := 
 ∀ (a₀ : Prop),
  ∀ (b₀ : Prop),
   (((a₀ ∨ b₀) = a₀) ∨ ((a₀ ∨ b₀) = b₀))
end F
