desugar_unresolved_var =
    cannot find value `{$var}` in this scope
    .label = not found in this scope

desugar_unresolved_dot_var =
    invalid use of refinement parameter
    .label = did you mean one of {$msg}?

desugar_duplicate_param =
    the name `{$name}` is already used as a parameter
    .label = already used

desugar_unresolved_sort =
    cannot find sort `{$sort}` in this scope
    .label = not found in this scope

desugar_int_too_large =
    integer literal is too large

desugar_unexpected_literal =
    unexpected literal

desugar_refined_type_param =
    type parameters cannot be refined
    .label = this type parameter has a refinement

desugar_invalid_dot_var =
    unsupported field access in refinement

desugar_unresolved_dot_field =
    cannot find `{$ident}.{$field}` in this scope

desugar_param_count_mismatch =
    this type takes {$expected} refinement parameters but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected} arguments, found {$found}

desugar_invalid_dot_access =
    the field `{$fld}` is not valid for param `{$ident}`
