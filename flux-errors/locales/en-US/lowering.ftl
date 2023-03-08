lowering_unsupported_mir =
    unsupported {$kind}
    .note = {$reason}

lowering_unsupported_local_decl =
    unsupported local declaration
    .label = this declaration has type `{$ty}` which is not currently supported

lowering_unsupported_type_of =
    unsupported type `{$ty}`
    .note = {$reason}

lowering_unsupported_fn_sig =
    unsupported signature

lowering_unsupported_generic_param =
    unsupported generic param

lowering_unsupported_generic_bound =
    unsupported generic bound
    .note = {$reason}
