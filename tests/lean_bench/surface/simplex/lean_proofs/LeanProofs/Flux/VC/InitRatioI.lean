import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def InitRatioI := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ∀ (j₀ : Int),
    (0 < m₀) ->
     (0 < n₀) ->
      ((0 < j₀) ∧ (j₀ < n₀)) ->
       (m₀ ≥ 0) ->
        (n₀ ≥ 0) ->
         (j₀ ≥ 0) ->
          (((k0 1 m₀ n₀ j₀))) ∧
          (∀ (i₀ : Int),
           ((k0 i₀ m₀ n₀ j₀)) ->
            (i₀ < m₀) ->
             ∀ (a'₁ : Prop),
              ((¬a'₁) ->
               ((k0 (i₀ + 1) m₀ n₀ j₀))) ∧
              (a'₁ ->
               (0 < i₀))
              )
          
end F
