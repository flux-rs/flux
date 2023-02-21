hir_annot_check_array_len_mismatch =
    array length mismatch
    .label = expected {$hir_len}, found {$flux_len}
    .hir_label = expected length

hir_annot_check_expected_default_return =
    return type mismatch
    .label = refined signature has a return type
    .default_return = rust signature has no return type

hir_annot_check_missing_return_type =
    missing return type
    .label = refined signature has no return type
    .hir_ret = rust signature has a return type

hir_annot_check_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$hir_type}`
    .hir_label = must be a valid refinement of this type
    .note = {$note}

hir_annot_check_fun_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$flux_args} {$flux_args ->
        [one] argument
        *[other] arguments
     }
    .hir_label = rust signature has {$hir_args} {$hir_args ->
        [one] argument
        *[other] arguments
    }

hir_annot_check_unresolved_location =
    cannot resolve `{$loc}`: only `&strg` variables can appear in ensures clauses
    .label = maybe annotate as `&strg`

hir_annot_check_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$flux_fields} {$flux_fields ->
        [one] field
        *[other] fields
     }
    .hir_label = rust variant has {$hir_fields} {$hir_fields ->
        [one] field
        *[other] fields
    }

hir_annot_check_generic_argument_count_mismatch =
    this {$def_kind} must take {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    }
    .hir_label = {$def_kind} used here with {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    }
