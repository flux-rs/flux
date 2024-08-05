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

middle_unsupported_generic_bound =
    unsupported generic bound
    .note = {$reason}

# Query Errors

middle_query_unsupported =
    unsupported signature
    .note = {$reason}

middle_query_invalid_generic_arg =
    cannot instantiate base generic with opaque type or a type parameter of kind type

middle_query_invalid_assoc_reft =
    invalid associated refinement for this function call

middle_query_ignored_item =
    use of ignored item

# Query Errors reported at use site

middle_query_unsupported_at =
    use of unsupported {$kind}
    .note = this {$kind} has unsupported features

middle_query_ignored_at =
    use of ignored {$kind} `{$name}`
    .label = help: try ignoring or trusting this code
