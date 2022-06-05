refineck-goto-error =
    error jumping to join point

refineck-call-error =
    precondition might not hold
    .label = precondition might not hold in this function call

refineck-assign-error =
    missmatched type in assignment
    .label = this assignment might be unsafe

refineck-ret-error =
    postcondition might not hold
    .label = the postcondition in this function might not hold

refineck-div-error =
    possible division by zero
    .label = denominator might be zero

refineck-rem-error =
    possible reminder with a divisor of zero
    .label = divisor might no be zero

refineck-assert-error =
    assertion might fail: {$msg}

refineck-param-inference-error =
    parameter inference error at function call
