wf_sort_mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

wf_param_count_mismatch =
    this type takes {$expected} refinement parameters but {$found ->
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
