# Desugar

desugar_unresolved_var =
    cannot find value `{$var}` in this scope
    .label = not found in this scope

desugar_duplicate_param =
    the name `{$name}` is already used as a parameter
    .label = already used
    .first_use = first use of `{$name}`

desugar_unresolved_sort =
    cannot find sort `{$sort}` in this scope
    .label = not found in this scope

desugar_int_too_large =
    integer literal is too large

desugar_unexpected_literal =
    unexpected literal

desugar_invalid_dot_var =
    unsupported field access in refinement

desugar_refine_arg_count_mismatch =
    this type takes {$expected ->
        [0] 0 refinement arguments
        [one] 1 refinement argument
        *[other] 1 or {$expected} refinement arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected ->
        [0] 0 refinement arguments
        [one] {$expected} argument
        *[other] 1 or {$expected} arguments
    }, found {$found}

desugar_invalid_unrefined_param =
    invalid use of refinement parameter
    .label = parameter `{$var}` refers to a type with no indices

desugar_illegal_binder =
    illegal binder
    .label = `{$kind}` binder not allowed in this position

desugar_invalid_numeric_suffix =
    invalid suffix `{$suffix}` for number literal
    .label = the suffix must be one of the numeric sorts `int` or `real`

desugar_refined_unrefinable_type =
    type cannot be refined

# Resolve errors

desugar_unsupported_signature =
    unsupported function signature
    .note = {$note}

desugar_unresolved_path =
    cannot resolve `{$path}`
    .help = flux can only resolve a path if it is present in the definition being refined


# Annot check

desugar_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_ty}`
    .expected_label = must be a valid refinement of this type
    .note = {$note}

desugar_fun_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$args} {$args ->
        [one] argument
        *[other] arguments
     }
    .expected_label = rust signature has {$expected_args} {$expected_args ->
        [one] argument
        *[other] arguments
    }

desugar_generic_argument_count_mismatch =
    this {$def_descr} must take {$expected} generic {$expected ->
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
    .expected_label = {$def_descr} used here with {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    }

desugar_array_len_mismatch =
    array length mismatch
    .label = expected {$expected_len}, found {$len}
    .expected_label = expected length

desugar_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$fields} {$fields ->
        [one] field
        *[other] fields
     }
    .expected_label = rust variant has {$expected_fields} {$expected_fields ->
        [one] field
        *[other] fields
    }
