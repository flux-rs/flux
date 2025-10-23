import LeanProofs.Instance

def fluxDefsInstance : FluxDefs := inferInstance

def VSeq := fluxDefsInstance.VSeq
def svec_vseq_empty : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) := fluxDefsInstance.svec_vseq_empty
def svec_vseq_singleton : {t0 : Type} -> [Inhabited t0] -> (t0 -> (VSeq t0)) := fluxDefsInstance.svec_vseq_singleton
def svec_vseq_append : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> ((VSeq t0) -> (VSeq t0))) := fluxDefsInstance.svec_vseq_append
def svec_vseq_get : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> t0)) := fluxDefsInstance.svec_vseq_get
def svec_vseq_set : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (t0 -> (VSeq t0)))) := fluxDefsInstance.svec_vseq_set
def svec_vseq_slice : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (Int -> (VSeq t0)))) := fluxDefsInstance.svec_vseq_slice
def svec_vseq_len : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> Int) := fluxDefsInstance.svec_vseq_len
