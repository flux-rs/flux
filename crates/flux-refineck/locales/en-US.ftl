# Refinememt checking errors

refineck_goto_error = error jumping to join point

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

refineck_unsupported_call =
    unsupported type in function call
    .function_definition = function defined here

refineck_expected_neg =
    {$def_descr} marked with `#[should_fail]` didn't produce a refinement type error

# Invariant checking

refineck_invalid_invariant =
    invariant cannot be proven

# Check impl against trait errors

refineck_incompatible_sort =
    implemented associated refinement `{$name}` has an incompatible sort for trait
    .label = expected `{$expected}`, found `{$found}`

refineck_invalid_assoc_reft =
    associated refinement `{$name}` is not a member of trait `{$trait_}`

refineck_missing_assoc_reft =
    associated refinement `{$name}` is missing from implementation

refineck_impl_assoc_reft_final =
    associated refinement `{$name}` is final and should not be implemented anywhere other than the trait definition
