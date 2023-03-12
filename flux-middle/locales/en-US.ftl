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

middle_unsupported_type_of =
    unsupported type `{$ty}`
    .note = {$reason}

middle_unsupported_fn_sig =
    unsupported signature

middle_unsupported_generic_param =
    unsupported generic param

middle_unsupported_generic_bound =
    unsupported generic bound
    .note = {$reason}

# Definition cycle

middle_definition_cycle =
    cycle in definitions
    .label = {$msg}
