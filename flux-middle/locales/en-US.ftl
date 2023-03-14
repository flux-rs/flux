# Lifting Errors

middle_unsupported_hir =
    refinement of unsupported {$def_kind}
    .label = this {$def_kind} contains unsupported features
    .note = {$note}

# Lowering Errors

middle_unsupported_mir =
    unsupported {$kind}
    .note = {$reason}

middle_unsupported_local_decl =
    unsupported local declaration
    .label = this declaration has type `{$ty}` which is not currently supported

middle_unsupported_fn_sig =
    unsupported signature

middle_unsupported_generic_param =
    unsupported generic param

middle_unsupported_generic_bound =
    unsupported generic bound
    .note = {$reason}

# Query Errors

middle_query_unsupported_type =
    unsupported type
    .note = {$reason}
