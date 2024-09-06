driver_duplicated_attr =
    duplicated attribute `{$name}`

driver_invalid_attr =
    invalid flux attribute

driver_cfg_error =
    invalid flux configuration: {$message}

driver_syntax_err =
    syntax error: {$msg}

driver_invalid_alias_application =
    invalid alias application

driver_attr_on_opaque =
    opaque struct can't have refined fields
    .label = this field has a refinement type annotation

driver_missing_variant =
    missing variant annotation
    .label = this variant doesn't have a refinement annotation
    .note = all variants in a refined enum must be annotated


driver_mismatched_spec_name =
    name in {$def_descr} spec doesn't match item's name
    .label = must be `{$item_ident}`
    .item_def_ident = {$def_descr} defined here


# Extern specs

driver_malformed_extern_spec =
    malformed extern_spec, this should never happen if you are using the extern_spec macro. Did you accidentally use the internal flux::extern_spec attribute?

driver_invalid_inherent_impl =
    all items in an extern spec must belong to the same impl block

driver_item_not_in_trait_impl =
    invalid extern spec for trait impl
    .label = `{$name}` is not defined in extern trait impl
    .note = extern trait impl defined here

