driver_duplicated_attr =
    duplicated attribute `{$name}`

driver_invalid_attr =
    invalid flux attribute

driver_invalid_attr_map =
    invalid attribute: {$message}

driver_unresolved_specification =
    unresolved {$thing} `{$ident}`

driver_multiple_specifications =
    multiple specifications for `{$name}`

driver_syntax_err =
    syntax error

driver_invalid_alias_application =
    invalid alias application

driver_mutable_static_spec =
    specifications on mutable statics are not yet supported

driver_attr_on_opaque =
    opaque struct can't have refined fields
    .label = this field has a refinement type annotation

driver_reflected_enum_with_refined_by =
    reflected enum with `refined_by` annotation
    .label = this enum can either be `reflected` or have a `refined_by` but not both

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

driver_invalid_enum_extern_spec =
    invalid extern_spec for enum: {$reason}

driver_cannot_resolve_trait_impl =
    cannot resolve trait implementation
    .note = this is probably a bug in Flux

driver_invalid_impl_block =
    invalid impl extern spec
    .label = items in this extern spec are not defined in the same extern impl block

driver_item_not_in_trait_impl =
    invalid extern spec for trait impl
    .label = `{$name}` is not defined in extern trait impl
    .note = extern trait impl defined here

driver_invalid_item_in_inherent_impl =
    invalid extern spec for inherent impl
    .label = `{$name}` is not a member of an inherent impl
    .note = `{$name}` defined here

driver_item_not_in_trait =
    invalid extern spec for trait
    .label = `{$name}` is not defined in extern trait
    .note = extern trait defined here

driver_extern_spec_for_local_def =
    cannot add extern specs to local definition
    .help = `{$name}` defined here in the same crate, use a detached spec https://flux-rs.github.io/flux/guide/specifications.html?highlight=detached#detached-specifications


driver_dup_extern_spec =
    multiple extern specs for `{$name}`
    .label = extern spec for `{$name}` redefined here
    .note = previous extern spec for `{$name}` defined here

driver_mismatched_generics =
    invalid extern spec for {$def_descr}
    .label = generic parameters don't match the external {$def_descr}
    .extern_def_label = external {$def_descr} found here
    .note = extern specs must exactly match the external definition, including the list of generic parameters and their names
