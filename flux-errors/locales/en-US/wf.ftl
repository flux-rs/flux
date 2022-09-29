wf-sort-mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

wf-param-count-mismatch =
    this type takes {$expected} refinement parameters but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected} arguments, found {$found}

wf-illegal-binder =
    illegal binder
    .label = binder not allowed under ADT parameter