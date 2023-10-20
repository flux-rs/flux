<img
    src="assets/logo-wide.svg"
    alt="flux logo" class="flux-logo">

`flux` is a refinement type checker for Rust.

# Online Demo

You can try `flux` [online at this site](https://flux.programming.systems)

# Overview

For an overview, take a look at the [`flux` website](https://flux-rs.github.io).

# Docs

Documentation, including installation and usage guides can be found on the
[website](https://flux-rs.github.io/flux).

-----
fn sort_params(
    generics: &rustc_middle::ty::Generics,
    refined_by: &surface::RefinedBy,
) -> Vec<DefId> {
    let sort_params: FxHashSet<_> = refined_by
        .sort_params
        .iter()
        .map(|ident| ident.name)
        .collect();
    let mut params = vec![];
    for param in &generics.params {
        if let rustc_middle::ty::GenericParamDefKind::Type { .. } = param.kind &&
           sort_params.contains(&param.name)
        {
            params.push(param.def_id);
        }
    }
    params
}