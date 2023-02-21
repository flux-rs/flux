parse_duplicated_attr =
    duplicated attribute `{$name}`

parse_invalid_attr =
    invalid flux attribute

parse_cfg_error =
    invalid flux configuration: {$message}

parse_syntax_err =
    syntax error: {$msg}

parse_invalid_constant =
    invalid constant

parse_invalid_alias_application =
    invalid alias application

parse_attr_on_opaque =
    opaque struct can't have field annotations
    .label = this field has a refinement annotation

parse_missing_variant =
    missing variant annotation
    .label = this variant doesn't have a refinement annotation
    .note = all variants in a refined enum must be annotated
