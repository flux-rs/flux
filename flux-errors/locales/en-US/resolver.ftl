resolver_unsupported_signature =
    unsupported function signature
    .note = {$msg}

resolver_unresolved_path =
    cannot resolve `{$path}`
    .help = flux can only resolve a path if it is present in the definition being refined

resolver_unresolved_location =
    cannot resolve `{$loc}`: only `&strg` variables can appear in ensures clauses
    .label = maybe annotate as `&strg`

resolver_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$flux_args} {$flux_args ->
        [one] argument
        *[other] arguments
     }
    .rust_label = rust signature has {$rust_args} {$rust_args ->
        [one] argument
        *[other] arguments
    }

resolver_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$flux_fields} {$flux_fields ->
        [one] field
        *[other] fields
     }
    .rust_label = rust variant has {$rust_fields} {$rust_fields ->
        [one] field
        *[other] fields
    }

resolver_path_mismatch =
    mismatched types
    .label =  expected `{$rust_type}`, found `{$flux_type}`
    .def_label = refinement annotation for this {$def_kind} is invalid

resolver_invalid_refinement =
    invalid refinement annotation
    .label = not a valid refinement of `{$rust_type}`
    .def_label = refinement annotation for this {$def_kind} is invalid

resolver_mutability_mismatch =
    mismatched types
    .label = types differ in mutability
    .def_label = refinement annotation for this {$def_kind} is invalid

resolver_default_return_mismatch =
    return type mismatch
    .label = expected `{$rust_type}`, found `()`
    .def_label = refinement annotation for this {$def_kind} is invalid

resolver_too_few_arguments =
    this {$def_kind} takes at least {$min} generic {$min ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected at least {$min} generic {$min ->
        [one] argument
        *[other] arguments
    }
    .note = {$def_kind} defined here

resolver_too_many_arguments =
    this {$def_kind} takes at most {$max} generic {$max ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected at most {$max} generic {$max ->
        [one] argument
        *[other] arguments
    }
    .note = {$def_kind} defined here

