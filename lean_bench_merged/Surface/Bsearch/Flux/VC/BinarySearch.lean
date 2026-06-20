import Surface.Bsearch.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BinarySearch := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (items₀ : Int),
   (0 ≤ items₀) ->
    (items₀ ≥ 0) ->
     (¬(items₀ ≤ 0)) ->
      (((items₀ - 1) ≥ 0)) ∧
      (((k0 0 (items₀ - 1) k₀ items₀))) ∧
      (∀ (low₀ : Int),
       ∀ (high₀ : Int),
        ((k0 low₀ high₀ k₀ items₀)) ->
         (low₀ ≤ high₀) ->
          (((high₀ - low₀) ≥ 0)) ∧
          ((((low₀ + ((high₀ - low₀) / 2)) < items₀)) ∧
          (∀ (a'₄ : Int),
           ((k1 a'₄ k₀ items₀ low₀ high₀))) ∧
          (∀ (a'₅ : Int),
           ((k1 a'₅ k₀ items₀ low₀ high₀)) ->
            (a'₅ ≠ k₀) ->
             ((¬(a'₅ > k₀)) ->
              ((k2 high₀ k₀ items₀ low₀ high₀ a'₅))) ∧
             ((a'₅ > k₀) ->
              ((low₀ + ((high₀ - low₀) / 2)) ≠ 0) ->
               ((((low₀ + ((high₀ - low₀) / 2)) - 1) ≥ 0)) ∧
               (((k2 ((low₀ + ((high₀ - low₀) / 2)) - 1) k₀ items₀ low₀ high₀ a'₅)))
               ) ∧
             (∀ (high₁ : Int),
              ((k2 high₁ k₀ items₀ low₀ high₀ a'₅)) ->
               ((¬(a'₅ < k₀)) ->
                ((k3 low₀ k₀ items₀ low₀ high₀ a'₅ high₁))) ∧
               ((a'₅ < k₀) ->
                ((k3 ((low₀ + ((high₀ - low₀) / 2)) + 1) k₀ items₀ low₀ high₀ a'₅ high₁))) ∧
               (∀ (low₁ : Int),
                ((k3 low₁ k₀ items₀ low₀ high₀ a'₅ high₁)) ->
                 ((k0 low₁ high₁ k₀ items₀)))
               )
             )
          )
          )
      
end F
