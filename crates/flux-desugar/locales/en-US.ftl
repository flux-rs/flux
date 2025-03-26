# Desugar

desugar_invalid_alias_reft =
    invalid alias refinement
    .label = this must be a trait

desugar_int_too_large =
    integer literal is too large

desugar_unexpected_literal =
    unexpected literal

desugar_invalid_dot_var =
    unsupported field access in refinement

desugar_invalid_constructor_path =
    invalid use of path in constructor

desugar_invalid_loc =
    expected an `&strg` parameter

desugar_invalid_numeric_suffix =
    invalid suffix `{$suffix}` for number literal
    .label = the suffix must be one of the numeric sorts `int` or `real`

desugar_unresolved_generic_param =
    cannot resolve generic param
    .note = generic parameters in refined signature must much rust signature

desugar_invalid_variant_ret =
    invalid variant return type

desugar_invalid_reflected_variant =
    reflected types cannot have refinement annotations

desugar_multiple_spreads_in_constructor =
    multiple spreads found in constructor
    .help = previous spread found here. consider removing it

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

desugar_unresolved_var =
    cannot find value `{$var}` in this scope
    .label = not found in this scope

desugar_unresolved_sort =
    cannot find sort `{$name}` in this scope
    .label = not found in this scope

desugar_invalid_unrefined_param =
    invalid use of refinement parameter
    .label = parameter `{$var}` refers to a type with no indices

desugar_illegal_binder =
    illegal binder
    .label = `{$kind}` binder not allowed in this position

desugar_unknown_qualifier =
    unknown qualifier


# Lifting Errors

desugar_unsupported_hir =
    refinement of unsupported {$def_kind}
    .label = this {$def_kind} contains unsupported features
    .note = {$note}
