import Surface.Date.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MkDate := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (day₀ : Int),
  ∀ (month₀ : Int),
   ∀ (year₀ : Int),
    (day₀ ≥ 0) ->
     (month₀ ≥ 0) ->
      (year₀ ≥ 0) ->
       (1 ≤ year₀) ->
        (1 ≤ month₀) ->
         (month₀ ≤ 12) ->
          (1 ≤ day₀) ->
           (day₀ ≤ 31) ->
            ((¬((((month₀ = 4) ∨ (month₀ = 6)) ∨ (month₀ = 9)) ∨ (month₀ = 11))) ->
             ((k0 day₀ month₀ year₀))) ∧
            (((((month₀ = 4) ∨ (month₀ = 6)) ∨ (month₀ = 9)) ∨ (month₀ = 11)) ->
             (day₀ ≤ 30) ->
              ((k0 day₀ month₀ year₀))) ∧
            (((k0 day₀ month₀ year₀)) ->
             ((¬(month₀ ≠ 2)) ->
              ((day₀ ≤ 29) ∧ ((day₀ = 29) -> (((year₀ % 400) = 0) ∨ (((year₀ % 4) = 0) ∧ ((year₀ % 100) > 0))))) ->
               ((k1 day₀ month₀ year₀))) ∧
             ((month₀ ≠ 2) ->
              ((k1 day₀ month₀ year₀))) ∧
             (((k1 day₀ month₀ year₀)) ->
              (((((month₀ = 4) ∨ (month₀ = 6)) ∨ (month₀ = 9)) ∨ (month₀ = 11)) ->
               (day₀ ≤ 30)) ∧
              ((month₀ = 2) ->
               ((day₀ ≤ 29)) ∧
               ((day₀ = 29) ->
                (((year₀ % 400) = 0) ∨ (((year₀ % 4) = 0) ∧ ((year₀ % 100) > 0))))
               )
              )
             )
            
end F
