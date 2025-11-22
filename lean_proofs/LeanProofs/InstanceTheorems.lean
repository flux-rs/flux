import LeanProofs.InferredInstance

theorem vseq_singleton_singleton [Inhabited a] (v: a): svec_vseq_singleton v = [v] := rfl
theorem vseq_len_len [Inhabited a] (l : List a) : svec_vseq_len l = Int.ofNat l.length := rfl
theorem vseq_append_append (l1 l2 : List Int) : svec_vseq_append l1 l2 = List.append l1 l2 := rfl
theorem vseq_get_get (l1 : List Int) (idx : Int) : svec_vseq_get l1 idx = list_get l1 idx := rfl
theorem vseq_empty_empty [Inhabited a] : (svec_vseq_empty : VSeq a) = [] := rfl
