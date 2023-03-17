driver_duplicated_attr =
    duplicated attribute `{$name}`

driver_invalid_attr =
    invalid flux attribute

driver_cfg_error =
    invalid flux configuration: {$message}

driver_syntax_err =
    syntax error: {$msg}

driver_invalid_constant =
    invalid constant

driver_invalid_alias_application =
    invalid alias application

driver_attr_on_opaque =
    opaque struct can't have field annotations
    .label = this field has a refinement annotation

driver_missing_variant =
    missing variant annotation
    .label = this variant doesn't have a refinement annotation
    .note = all variants in a refined enum must be annotated

driver_malformed_extern_spec =
    malformed extern_spec, expecting a function definition with a call to the external method as the body

driver_missing_fn_sig_for_extern_spec =
    missing flux::sig attribute (functions declared as flux::extern_spec require a flux::sig)
