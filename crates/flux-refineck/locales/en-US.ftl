# Refinememt checking errors

refineck_goto_error =
    error jumping to join point

refineck_assign_error =
    assignment might be unsafe

refineck_condition_span_note =
    this is the condition that cannot be proved

refineck_call_span_note =
    inside this call

refineck_refine_error =
    refinement type error
    .label = a {$cond} cannot be proved

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
    cannot access fields of opaque struct `{$struct}`. 

refineck_opaque_struct_help =
    If you'd like to use fields of `{$struct}` in methods, use `flux::trusted` instead of `flux::opaque`.

refineck_unsupported_call =
    unsupported type in function call
    .function_definition = function defined here

refineck_expected_neg =
    {$def_descr} marked with `#[should_fail]` didn't produce a refinement type error

# Invariant checking

refineck_invalid_invariant =
    invariant cannot be proven
