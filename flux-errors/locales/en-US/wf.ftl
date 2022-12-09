wf_sort_mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

wf_param_count_mismatch =
    this {$thing} takes {$expected} refinement parameters but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected} arguments, found {$found}

wf_illegal_binder =
    illegal binder
    .label = binder not allowed in this position

wf_duplicated_ensures =
    an ensures clause already exists for `{$loc}`

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