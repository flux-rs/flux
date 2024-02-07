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

fhir_analysis_early_bound_arg_count_mismatch =
    this type alias takes {$expected ->
        [one] {$expected} early bound argument
        *[other] {$expected} early bound arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected ->
        [one] {$expected} early bound argument
        *[other] {$expected} early bound arguments
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

fhir_analysis_invalid_primitive_dot_access =
    `{$sort}` is a primitive sort and therefore doesn't have fields

fhir_analysis_expected_numeric =
    mismatched sorts
    .label = expected numeric sort, found `{$found}`

fhir_analysis_no_equality =
    values of sort `{$sort}` cannot be compared for equality

fhir_analysis_invalid_base_instance =
    values of this type cannot be used as base sorted instances

fhir_analysis_param_not_determined =
    parameter `{$sym}` cannot be determined
    .label = undetermined parameter
    .help = try indexing a type with `{$sym}` in a position that fully determines its value

fhir_analysis_sort_annotation_needed =
    sort annotation needed
    .label = help: consider giving this parameter an explicit sort

fhir_analysis_cannot_infer_sort =
    sort annotation needed
    .label = cannot infer sort
    .note = sort must be known at this point


fhir_analysis_refined_unrefinable_type =
    type cannot be refined

# Annot check

fhir_analysis_invalid_refinement =
    invalid refinement annotation
    .label = expected a refinement of `{$expected_ty}`
    .expected_label = must be a valid refinement of this type
    .note = {$note}

fhir_analysis_fun_arg_count_mismatch =
    argument count mismatch
    .label = refined signature has {$args} {$args ->
        [one] argument
        *[other] arguments
     }
    .expected_label = rust signature has {$expected_args} {$expected_args ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_generic_argument_count_mismatch =
    this {$def_descr} must take {$expected} generic {$expected ->
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
    .expected_label = {$def_descr} used here with {$expected} generic {$expected ->
        [one] argument
        *[other] arguments
    }

fhir_analysis_array_len_mismatch =
    array length mismatch
    .label = expected {$expected_len}, found {$len}
    .expected_label = expected length

fhir_analysis_field_count_mismatch =
    field count mismatch
    .label = refined variant has {$fields} {$fields ->
        [one] field
        *[other] fields
     }
    .expected_label = rust variant has {$expected_fields} {$expected_fields ->
        [one] field
        *[other] fields
    }

# Definition cycle

fhir_analysis_definition_cycle =
    cycle in definitions
    .label = {$msg}

# Conv errors

fhir_analysis_assoc_type_not_found =
    associated type not found
    .label = cannot resolve this associated type
    .note = Flux cannot resolved associated types if they are defined in a super trait

# Check impl against trait errors

fhir_analysis_incompatible_sort =
    implemented associated refinement `{$name}` has an incompatible sort for trait
    .label = expected `{$expected}`, found `{$found}`

fhir_analysis_invalid_assoc_reft =
    associated refinement `{$name}` is not a member of trait `{$trait_id}`
