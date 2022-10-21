resolver_unsupported_signature =
    unsupported function signature: `{$msg}`

resolver_unresolved_path =
    cannot resolve `{$path}`

resolver_unresolved_location =
    cannot resolve `{$loc}`: only `&strg` variables can appear in ensures clauses
    .label = maybe annotate as `&strg`

resolver_mismatched_args =
    arg count mismatch in flux signature: rust signature has {$rust_args} but flux signature has {$flux_args}

resolver_mismatched_fields =
    field count mismatch in flux signature: rust signature has {$rust_fields} but flux signature has {$flux_fields}

resolver_mismatched_type =
    type mismatch in flux signature
    .label =  expected `{$rust_type}`, found `{$flux_type}`

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

