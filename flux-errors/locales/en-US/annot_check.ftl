annot_check_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_ty}`
    .expected_label = must be a valid refinement of this type
    .note = {$note}

annot_check_invalid_refinement_path =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_path}`
    .expected_label = must be a valid refinement of this type
    .note = {$note}

annot_check_fun_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$args} {$args ->
        [one] argument
        *[other] arguments
     }
    .expected_label = rust signature has {$expected_args} {$expected_args ->
        [one] argument
        *[other] arguments
    }

annot_check_generic_argument_count_mismatch =
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

annot_check_array_len_mismatch =
    array length mismatch
    .label = expected {$expected_len}, found {$len}
    .expected_label = expected length

annot_check_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$fields} {$fields ->
        [one] field
        *[other] fields
     }
    .expected_label = rust variant has {$expected_fields} {$expected_fields ->
        [one] field
        *[other] fields
    }
