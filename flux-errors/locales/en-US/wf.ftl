wf_sort_mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

wf_arg_count_mismatch =
    this {$thing} takes {$expected ->
        [one] {$expected} refinement argument
        *[other] {$expected} refinement arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected ->
        [one] {$expected} argument
        *[other] {$expected} arguments
    }, found {$found}

wf_early_bound_arg_count_mismatch =
    this type alias takes {$expected ->
        [one] {$expected} early bound argument
        *[other] {$expected} early bound arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected ->
        [one] {$expected} early bound argument
        *[other] {$expected} early bound arguments
    }, found {$found}

wf_illegal_binder =
    illegal binder
    .label = binder not allowed in this position

wf_duplicated_ensures =
    an ensures clause already exists for `{$loc}`

wf_unknown_qualifier =
    unknown qualifier

wf_missing_ensures =
    missing ensures clause for `&strg` reference

wf_expected_fun =
    expected function, found `{$found}`

wf_invalid_param_in_func_pos =
    illegal use of refinement parameter
    .label = {$is_pred ->
        [true] abstract refinements are only allowed in a top-level conjunction
        *[false] parameters of sort `{$sort}` are not supported in this position
     }

wf_unexpected_fun =
    mismatched sorts
    .label = expected `{$sort}`, found function

wf_definition_cycle =
    cycle in definitions
    .label = {$msg}

wf_param_count_mismatch =
    parameter count mismatch
    .label = this function has {$found ->
        [one] {$found} parameter
        *[other] {$found} parameters
    }, but a function with {$expected ->
        [one] {$expected} parameter
        *[other] {$expected} parameters
    } was expected

wf_field_not_found =
    no field `{$fld}` on sort `{$sort}`

wf_invalid_primitive_dot_access =
    `{$sort}` is a primitive sort and therefore doesn't have fields

wf_expected_numeric =
    mismatched sorts
    .label = expected numeric sort, found `{$found}`

wf_no_equality =
    values of sort `{$sort}` cannot be compared for equality
