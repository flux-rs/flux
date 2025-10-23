import LeanProofs.OpaqueFluxDefs

def slice {α : Type} (xs : List α) (left right : Int) : List α :=
  let len := xs.length
  -- Clamp indices into the valid [0, len] range
  let l := if left < 0 then 0 else if left > len then len else left.toNat
  let r := if right < 0 then 0 else if right > len then len else right.toNat
  if r ≤ l then
    []
  else
    xs.drop l |>.take (r - l)

def list_get (xs : List Int) (i : Int) : Int :=
  let n := xs.length
  if 0 ≤ i ∧ i < (n : Int) then
    match xs[i.toNat]? with
    | some v => v
    | none   => -1  -- should not happen because of the guard, but keep safe
  else
    -1

def set (xs : List Int) (i : Int) (v : Int) : List Int :=
  match xs, i with
  | [], _ => []
  | x :: xs', i =>
    if i = 0 then
      v :: xs'
    else if i > 0 then
      x :: set xs' (i - 1) v
    else
      x :: xs'  -- negative index, unchanged

instance : FluxDefs where
  ISeq := List Int
  svec_iseq_empty := []
  svec_iseq_singleton := fun x => [x]
  svec_iseq_append := List.append
  svec_iseq_get := list_get
  svec_iseq_slice := slice
  svec_iseq_len := fun x => Int.ofNat x.length
  svec_iseq_set := set
