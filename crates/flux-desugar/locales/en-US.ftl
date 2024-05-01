# Desugar

desugar_invalid_alias_reft =
    invalid alias refinement
    .label = this must be a trait

desugar_invalid_constant =
    invalid constant

desugar_int_too_large =
    integer literal is too large

desugar_unexpected_literal =
    unexpected literal

desugar_invalid_dot_var =
    unsupported field access in refinement

desugar_invalid_func_as_var =
    invalid use of function
    .label = function not supported in this position

desugar_invalid_func =
    invalid name in function position
    .label = expected a function or parameter

desugar_invalid_loc =
    expected an `&strg` parameter

desugar_invalid_numeric_suffix =
    invalid suffix `{$suffix}` for number literal
    .label = the suffix must be one of the numeric sorts `int` or `real`

desugar_unresolved_generic_param =
    cannot resolve generic param
    .note = generic parameters in refined signature must much rust signature

# Resolve errors

desugar_duplicate_param =
    the name `{$name}` is already used as a parameter
    .label = already used
    .first_use = first use of `{$name}`

desugar_unsupported_signature =
    unsupported function signature
    .note = {$note}

desugar_unresolved_path =
    cannot resolve `{$path}`
    .help = flux can only resolve a path if it is present in the definition being refined

desugar_unresolved_var =
    cannot find {$kind} `{$var}` in this scope
    .label = not found in this scope

desugar_unresolved_sort =
    cannot find sort `{$sort}` in this scope
    .label = not found in this scope

desugar_invalid_unrefined_param =
    invalid use of refinement parameter
    .label = parameter `{$var}` refers to a type with no indices

desugar_illegal_binder =
    illegal binder
    .label = `{$kind}` binder not allowed in this position
