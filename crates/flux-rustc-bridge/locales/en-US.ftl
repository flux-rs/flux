# Lowering Errors

rustc_bridge_unsupported_mir =
    unsupported {$kind}
    .note = {$reason}

rustc_bridge_unsupported_local_decl =
    unsupported local declaration
    .label = this declaration has type `{$ty}` which is not currently supported

rustc_bridge_unsupported_generic_bound =
    unsupported generic bound
    .note = {$reason}
