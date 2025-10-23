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

def list_get { a : Type } [Inhabited a] (xs : List a) (i : Int) : a :=
  let n := xs.length
  if 0 ≤ i ∧ i < (n : Int) then
    match xs[i.toNat]? with
    | some v => v
    | none   => (inferInstance : Inhabited a).default  -- should not happen because of the guard, but keep safe
  else
    (inferInstance : Inhabited a).default

def list_set { a : Type } (xs : List a) (i : Int) (v : a) : List a :=
  match xs, i with
  | [], _ => []
  | x :: xs', i =>
    if i = 0 then
      v :: xs'
    else if i > 0 then
      x :: list_set xs' (i - 1) v
    else
      x :: xs'  -- negative index, unchanged

instance : FluxDefs where
  VSeq (a : Type) [Inhabited a] := List a
  svec_vseq_empty := []
  svec_vseq_singleton := fun x => [x]
  svec_vseq_append := List.append
  svec_vseq_get := list_get
  svec_vseq_set := list_set
  svec_vseq_slice := slice
  svec_vseq_len := Int.ofNat ∘ List.length
