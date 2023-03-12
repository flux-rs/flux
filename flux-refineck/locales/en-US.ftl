# Refinememt checking errors

refineck_goto_error =
    error jumping to join point

refineck_call_error =
    precondition might not hold

refineck_assign_error =
    assignment might be unsafe

refineck_ret_error =
    postcondition might not hold

refineck_div_error =
    possible division by zero

refineck_rem_error =
    possible reminder with a divisor of zero

refineck_assert_error =
    assertion might fail: {$msg}

refineck_param_inference_error =
    parameter inference error at function call

refineck_fold_error =
    type invariant may not hold (when place is folded)

refineck_unknown_error =
    cannot prove this code safe

refineck_overflow_error =
    arithmetic operation may overflow

refineck_opaque_struct_error =
    cannot access fields of opaque struct `{$struct}`

refineck_unsupported_call =
    unsupported type in function call
    .function_definition = function defined here

# Well-formed errors

refineck_sort_mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

refineck_arg_count_mismatch =
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

refineck_early_bound_arg_count_mismatch =
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

refineck_illegal_binder =
    illegal binder
    .label = binder not allowed in this position

refineck_duplicated_ensures =
    an ensures clause already exists for `{$loc}`

refineck_unknown_qualifier =
    unknown qualifier

refineck_missing_ensures =
    missing ensures clause for `&strg` reference

refineck_expected_fun =
    expected function, found `{$found}`

refineck_invalid_param_in_func_pos =
    illegal use of refinement parameter
    .label = {$is_pred ->
        [true] abstract refinements are only allowed in a top-level conjunction
        *[false] parameters of sort `{$sort}` are not supported in this position
     }

refineck_unexpected_fun =
    mismatched sorts
    .label = expected `{$sort}`, found function

refineck_param_count_mismatch =
    parameter count mismatch
    .label = this function has {$found ->
        [one] {$found} parameter
        *[other] {$found} parameters
    }, but a function with {$expected ->
        [one] {$expected} parameter
        *[other] {$expected} parameters
    } was expected

refineck_field_not_found =
    no field `{$fld}` on sort `{$sort}`

refineck_invalid_primitive_dot_access =
    `{$sort}` is a primitive sort and therefore doesn't have fields

refineck_expected_numeric =
    mismatched sorts
    .label = expected numeric sort, found `{$found}`

refineck_no_equality =
    values of sort `{$sort}` cannot be compared for equality

# Invariant checking

refineck_invalid_invariant =
    invariant cannot be proven
