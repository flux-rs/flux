desugar_unresolved_var =
    cannot find value `{$var}` in this scope
    .label = not found in this scope

desugar_unresolved_dot_var =
    invalid use of refinement parameter
    .label = did you mean one of {$msg}?

desugar_duplicate_param =
    the name `{$name}` is already used as a parameter
    .label = already used
    .first_use = first use of `{$name}`

desugar_unresolved_sort =
    cannot find sort `{$sort}` in this scope
    .label = not found in this scope

desugar_int_too_large =
    integer literal is too large

desugar_unexpected_literal =
    unexpected literal

desugar_invalid_dot_var =
    unsupported field access in refinement

desugar_param_count_mismatch =
    this type takes {$expected} refinement parameters but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected} arguments, found {$found}

desugar_invalid_primitive_dot_access =
    `{$sort}` is a primitive sort and therefore doesn't have fields
    .label = field access on parameter `{$name}`
    .defined_here = `{$name}` defined here with sort `{$sort}`

desugar_invalid_unrefined_param =
    invalid use of parameter `{$var}`
    .label = parameter `{$var}` refers to a type with no indices
    .defined_here = declared here

desugar_field_not_found =
    no field `{$fld}` on refinement parameters for {$def_kind} `{$def_name}`

desugar_def_span_note =
    {$has_params ->
        [true] {$def_kind} defined here
        *[false] {$def_kind} defined here with no parameters
    }
