import LeanProofs.InferredInstance

theorem iseq_singleton_singleton (v: Int) : svec_iseq_singleton v = [v] := rfl
theorem iseq_len_len (l : List Int) : svec_iseq_len l = Int.ofNat l.length := rfl
theorem iseq_append_append (l1 l2 : List Int) : svec_iseq_append l1 l2 = List.append l1 l2 := rfl
theorem iseq_get_get (l1 : List Int) (idx : Int) : svec_iseq_get l1 idx = list_get l1 idx := rfl
theorem iseq_empty_empty : svec_iseq_empty = [] := rfl
