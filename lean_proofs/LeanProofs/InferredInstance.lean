import LeanProofs.Instance

def fluxDefsInstance : FluxDefs := inferInstance

def ISeq := fluxDefsInstance.ISeq
def svec_iseq_empty : ISeq := fluxDefsInstance.svec_iseq_empty
def svec_iseq_singleton : (Int -> ISeq) := fluxDefsInstance.svec_iseq_singleton
def svec_iseq_append : (ISeq -> (ISeq -> ISeq)) := fluxDefsInstance.svec_iseq_append
def svec_iseq_get : (ISeq -> (Int -> Int)) := fluxDefsInstance.svec_iseq_get
def svec_iseq_set : (ISeq -> (Int -> (Int -> ISeq))) := fluxDefsInstance.svec_iseq_set
def svec_iseq_slice : (ISeq -> (Int -> (Int -> ISeq))) := fluxDefsInstance.svec_iseq_slice
def svec_iseq_len : (ISeq -> Int) := fluxDefsInstance.svec_iseq_len
