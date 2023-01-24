hir_resolver_array_len_mismatch =
    array length mismatch
    .label = expected {$hir_len}, found {$flux_len}
    .hir_label = expected length

hir_resolver_unsupported_hir =
    refinement of unsupported {$def_kind}
    .label = this {$def_kind} contains unsupported features
    .note = {$note}

hir_resolver_expected_default_return =
    return type mismatch
    .label = refined signature has a return type
    .default_return = rust signature has no return type

hir_resolver_missing_return_type =
    missing return type
    .label = refined signature has no return type
    .hir_ret = rust signature has a return type

hir_resolver_mutability_mismatch =
    invalid refinement annotation
    .label = type differs in mutability
    .hir_label = rust reference has different mutability

hir_resolver_invalid_refinement =
    invalid refinement annotation
    .label = not a valid refinement of the corresponding rust type
    .hir_label = must be a valid refinement of this type

hir_resolver_fun_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$flux_args} {$flux_args ->
        [one] argument
        *[other] arguments
     }
    .hir_label = rust signature has {$hir_args} {$hir_args ->
        [one] argument
        *[other] arguments
    }
