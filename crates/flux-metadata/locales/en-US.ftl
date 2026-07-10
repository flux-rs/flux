metadata_decode_file_error = "error when decoding flux metadata file {$path}: {$err}"

metadata_incompatible_metadata =
    failed to decode flux metadata file `{$path}`; this is likely because it was produced by an incompatible version of flux. Run `cargo clean` to remove stale metadata and try again

metadata_duplicate_spec = "duplicate spec for {$def_name}"
