resolver_unsupported_signature =
    unsupported function signature: `{$msg}`

resolver_unresolved_path =
    cannot resolve `{$path}`

resolver_mismatched_args =
    arg count mismatch in flux signature: rust signature has {$rust_args} but flux signature has {$flux_args}

resolver_mismatched_fields =
    field count mismatch in flux signature: rust signature has {$rust_fields} but flux signature has {$flux_fields}

resolver_mismatched_type =
    type mismatch in flux signature: expected `{$rust_type}` but saw `{$flux_type}`

resolver_mutability_mismatch =
    mutability mismatch in flux signature: rust signature has a `{$rust_ref}` reference but flux signature has a `{$flux_ref}` reference
