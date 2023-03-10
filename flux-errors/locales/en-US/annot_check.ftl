annot_check_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_ty}`
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
