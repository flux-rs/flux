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

# Invariant checking

refineck_invalid_invariant =
    invariant cannot be proven
