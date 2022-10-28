resolver_unsupported_signature =
    unsupported function signature
    .note = {$msg}

resolver_unresolved_path =
    cannot resolve `{$path}`
    .help = flux can only resolve a path if it is present in the rust signature

resolver_unresolved_location =
    cannot resolve `{$loc}`: only `&strg` variables can appear in ensures clauses
    .label = maybe annotate as `&strg`

resolver_arg_count_mismatch =
    argument count mismatch
    .label = flux signature has {$flux_args} {$flux_args ->
        [one] argument
        *[other] arguments
     }
    .rust_label = rust signature has {$rust_args} {$rust_args ->
        [one] argument
        *[other] arguments
    }

resolver_field_count_mismatch =
    field count mismatch
    .label = flux variant has {$flux_fields} {$flux_fields ->
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

resolver_invalid_refinement =
    invalid type refinement
    .label = `{$flux_type}` is not a valid refinement of `{$rust_type}`

resolver_mutability_mismatch =
    mutability mismatch in flux signature: rust signature has a `{$rust_ref}` reference but flux signature has a `{$flux_ref}` reference

resolver_default_return_mismatch =
    return type mismatch in flux signature: expected `{$rust_type}`, found ()

resolver_too_few_arguments =
    this type takes at least {$min} generic {$min ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied

resolver_too_many_arguments =
    this type takes at most {$max} generic {$max ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied

