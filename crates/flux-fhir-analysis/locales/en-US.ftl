# Well-formed errors

fhir_analysis_sort_mismatch =
    mismatched sorts
    .label = expected `{$expected}`, found `{$found}`

fhir_analysis_arg_count_mismatch =
    this {$thing} takes {$expected ->
        [one] {$expected} refinement argument
        *[other] {$expected} refinement arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected ->
        [one] {$expected} argument
        *[other] {$expected} arguments
    }, found {$found}

fhir_analysis_illegal_binder =
    illegal binder
    .label = binder not allowed in this position

fhir_analysis_duplicated_ensures =
    an ensures clause already exists for `{$loc}`

fhir_analysis_unknown_qualifier =
    unknown qualifier

fhir_analysis_missing_ensures =
    missing ensures clause for `&strg` reference

fhir_analysis_invalid_constant =
    invalid constant specification for non-integral constant

fhir_analysis_expected_fun =
    expected function, found `{$found}`

fhir_analysis_invalid_param_in_func_pos =
    illegal use of refinement parameter
    .label = {$is_pred ->
        [true] abstract refinements are only allowed in a top-level conjunction
        *[false] parameters of sort `{$sort}` are not supported in this position
     }

fhir_analysis_unexpected_fun =
    mismatched sorts
    .label = expected `{$sort}`, found function

fhir_analysis_unexpected_constructor =
    mismatched sorts
    .label = expected `{$sort}`, found constructor

fhir_analysis_param_count_mismatch =
    parameter count mismatch
    .label = this function has {$found ->
        [one] {$found} parameter
        *[other] {$found} parameters
    }, but a function with {$expected ->
        [one] {$expected} parameter
        *[other] {$expected} parameters
    } was expected

fhir_analysis_field_not_found =
    no field `{$fld}` on sort `{$sort}`

fhir_analysis_constructor_missing_fields =
    missing fields in constructor: {$missing_fields}

fhir_analysis_duplicate_field_used =
    field `{$fld}` was previously used in constructor
    .help = field `{$fld}` previously used here, consider removing it

fhir_analysis_invalid_primitive_dot_access =
    `{$sort}` is a primitive sort and therefore doesn't have fields

fhir_analysis_expected_numeric =
    mismatched sorts
    .label = expected numeric sort, found `{$found}`

fhir_analysis_no_equality =
    values of sort `{$sort}` cannot be compared for equality

fhir_analysis_param_not_determined =
    parameter `{$name}` cannot be determined
    .label = undetermined parameter
    .help = try indexing a type with `{$name}` in a position that fully determines its value

fhir_analysis_sort_annotation_needed =
    sort annotation needed
    .label = help: consider giving this parameter an explicit sort

fhir_analysis_constant_annotation_needed =
    constant annotation required
    .label = help: non-integral constants need a `constant` annotation that specifies their refinement value

fhir_analysis_cannot_infer_sort =
    sort annotation needed
    .label = cannot infer sort
    .note = sort must be known at this point

# Structural Compatibility

fhir_analysis_incompatible_refinement =
    {$def_descr} has an incompatible refinement annotation
    .label = expected a refinement of `{$expected_ty}`
    .expected_label = unrefined {$def_descr} found here
    .note = a refinement annotation must match the unrefined definition structurally

fhir_analysis_incompatible_param_count =
    {$def_descr} has an incompatible refinement annotation
    .label = refined signature has {$found} {$found ->
        [one] parameter
        *[other] parameters
     }
    .expected_label = unrefined signature has {$expected} {$expected ->
        [one] parameter
        *[other] parameters
    }

fhir_analysis_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_ty}`
    .expected_label = must be a valid refinement of this type
    .note = {$note}

fhir_analysis_fun_arg_count_mismatch =
    {$def_descr} has an incompatible refinement annotation
    .label = refined signature has {$args} {$args ->
        [one] argument
        *[other] arguments
     }
    .expected_label = unrefined signature has {$expected_args} {$expected_args ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_array_len_mismatch =
    array length mismatch
    .label = expected {$expected_len}, found {$len}
    .expected_label = expected length

fhir_analysis_field_count_mismatch =
    variant has an incompatible refinement annotation
    .label = expected {$expected_fields} {$expected_fields ->
        [one] field
        *[other] fields
     }, found {$fields}
    .expected_label = unrefined variant defined here

# Definition cycle

fhir_analysis_definition_cycle =
    cycle in definitions
    .label = {$msg}

# Conv errors

fhir_analysis_assoc_type_not_found =
    associated type not found
    .label = cannot resolve this associated type
    .note = Flux cannot resolved associated types if they are defined in a super trait

fhir_analysis_ambiguous_assoc_type =
    ambiguous associated type `{$name}`
    .label = help: use fully-qualified syntax

fhir_analysis_invalid_base_instance =
    values of this type cannot be used as base sorted instances

fhir_analysis_generic_argument_count_mismatch =
    this {$def_descr} takes {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_too_few_generic_args =
    this {$def_descr} takes at least {$min} generic {$min ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected at least {$min} generic {$min ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_too_many_generic_args =
    this {$def_descr} takes at most {$max} generic {$max ->
        [one] argument
        *[other] arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected at most {$max} generic {$max ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_generics_on_primitive_sort =
    primitive sort {$name} expects {$expected ->
        [0] no generics
        [one] exactly one generic argument
        *[other] exactly {$expected} generic arguments
    } but found {$found}
    .label = incorrect generics on primitive sort

fhir_analysis_incorrect_generics_on_sort =
    sorts associated with this {$def_descr} should have {$expected ->
        [0] no generic arguments
        [one] one generic argument
        *[other] {$expected} generic arguments
    } but {$found} generic {$found ->
        [one] argument was
        *[other] arguments were
    } supplied
    .label = expected {$expected ->
        [0] no generic arguments
        [one] one generic argument
        *[other] {$expected} generic arguments
    } on sort

fhir_analysis_generics_on_sort_ty_param=
    type parameter expects no generics but found {$found}
    .label = found generics on sort type parameter

fhir_analysis_generics_on_self_alias =
    type alias Self expects no generics but found {$found}
    .label = found generics on type `Self`

fhir_analysis_fields_on_reflected_enum_variant =
    reflected enum variants cannot have any fields
    .label = found fields on reflected enum variant

fhir_analysis_generics_on_opaque_sort =
    user defined opaque sorts have no generics but found {$found}
    .label = found generics on user defined opaque sort

fhir_analysis_refined_unrefinable_type =
    type cannot be refined

fhir_analysis_generics_on_prim_ty =
    generic arguments are not allowed on builtin type `{$name}`

fhir_analysis_generics_on_ty_param =
    generic arguments are not allowed on type parameter `{$name}`

fhir_analysis_generics_on_self_ty =
    generic arguments are not allowed on self type

fhir_analysis_generics_on_foreign_ty =
    generic arguments are not allowed on foreign types

fhir_analysis_invalid_assoc_reft =
    associated refinement `{$name}` is not a member of trait `{$trait_}`

fhir_analysis_refine_arg_mismatch =
    {$kind} takes {$expected} generic refinement {$expected ->
        [one] argument
        *[other] arguments
    }, but {$found} {$found ->
        [one] argument was
        *[other] arguments were
    } provided
    .label = expected {$expected} generic refinement {$expected ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_expected_type =
    expected a type, found {$def_descr} `{$name}`

fhir_analysis_fail_to_match_predicates =
    cannot determine corresponding unrefined predicate
    .note = you can only add a refined predicate if an corresponding unrefined one exists
