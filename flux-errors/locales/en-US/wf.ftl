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
    .label = binder not allowed under ADT parameter

wf_unresolved_function =
    unresolved function
    .label = function is not defined in this scope
