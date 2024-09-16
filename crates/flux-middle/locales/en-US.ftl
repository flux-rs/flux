# Lifting Errors

middle_unsupported_hir =
    refinement of unsupported {$def_kind}
    .label = this {$def_kind} contains unsupported features
    .note = {$note}

# Query Errors

middle_query_unsupported =
    unsupported signature
    .note = {$reason}

middle_query_invalid_generic_arg =
    cannot instantiate base generic with opaque type or a type parameter of kind type

middle_query_invalid_assoc_reft =
    associated refinement `{$name}` is not defined in this trait implementation

middle_query_bug =
    internal flux error: {$location}

middle_query_ignored_item =
    use of ignored item

# Query Errors reported at use site

middle_query_unsupported_at =
    use of unsupported {$kind}
    .note = this {$kind} has unsupported features

middle_query_ignored_at =
    use of ignored {$kind} `{$name}`
    .label = help: try ignoring or trusting this code

middle_query_invalid_assoc_reft_at =
    invalid associated refinement for this function call
