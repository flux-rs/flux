desugar-unresolved-var =
    cannot find value `{$var}` in this scope
    .label = not found in this scope

desugar-unresolved-dot-var =
    invalid use of refinement parameter
    .label = did you mean one of {$msg}?

desugar-duplicate-param =
    the name `{$name}` is already used as a parameter
    .label = already used

desugar-unresolved-sort =
    cannot find sort `{$sort}` in this scope
    .label = not found in this scope

desugar-int-too-large =
    integer literal is too large

desugar-unexpected-literal =
    unexpected literal

desugar-refined-type-param =
    type parameters cannot be refined
    .label = this type parameter has a refinement

desugar-invalid-array-len =
    unsupported or invalid array length

desugar-invalid-dot-var =
    unsupported field access in refinement

desugar-unresolved-dot-field =
    cannot find `{$ident}.{$field}` in this scope

desugar-param-count-mismatch =
    this type takes {$expected} refinement parameters but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }
    .label = expected {$expected} arguments, found {$found}
