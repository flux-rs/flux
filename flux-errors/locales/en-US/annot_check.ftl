annot_check_unresolved_location =
    cannot resolve `{$loc}`: only `&strg` variables can appear in ensures clauses
    .label = maybe annotate as `&strg`

annot_check_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$flux_args} {$flux_args ->
        [one] argument
        *[other] arguments
     }
    .rust_label = rust signature has {$rust_args} {$rust_args ->
        [one] argument
        *[other] arguments
    }

annot_check_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$flux_fields} {$flux_fields ->
        [one] field
        *[other] fields
     }
    .rust_label = rust variant has {$rust_fields} {$rust_fields ->
        [one] field
        *[other] fields
    }

annot_check_path_mismatch =
    mismatched types
    .label =  expected `{$rust_type}`, found `{$flux_type}`

annot_check_invalid_refinement =
    invalid refinement annotation
    .label = not a valid refinement of `{$rust_type}`

annot_check_mutability_mismatch =
    mismatched types
    .label = types differ in mutability

annot_check_default_return_mismatch =
    return type mismatch
    .label = expected `{$rust_type}`, found `()`

annot_check_too_few_arguments =
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

annot_check_too_many_arguments =
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

annot_check_invalid_refinement_for_def =
    refinement annotation for this {$def_kind} is invalid

annot_check_definition_span_note =
    {$def_kind} defined here
