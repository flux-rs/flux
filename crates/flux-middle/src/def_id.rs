use flux_common::bug;
use rustc_hir::def_id::{DefId, DefIndex, LocalDefId};
use rustc_macros::{Decodable, Encodable};
use rustc_span::Symbol;

/// An id for an Flux item with a type-level invariant ensuring that it exists.
///
/// We represent the id as a Rust parent id and an the name of the item. Since the name can be an
/// arbitrary [`Symbol`], this doesn't guarantee the existence of the item, so we must be careful
/// when creating instances of this struct.
///
/// We make the struct fields private so we have to create one using [`FluxId::new`]. We also
/// have a clippy lint disallowing [`FluxDefId::new`] which can be disabled selectively when we can
/// ensure the associated refinement exists.
///
/// The struct is generic on the parent `Id` because we use it with various kinds of ids,
/// e.g., [`DefId`], [`MaybeExternId`], ...
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Encodable, Decodable)]
pub struct FluxId<Id> {
    parent: Id,
    name: Symbol,
}

pub type FluxDefId = FluxId<DefId>;
pub type FluxLocalDefId = FluxId<LocalDefId>;

impl<Id> FluxId<Id> {
    pub fn new(parent: Id, name: Symbol) -> Self {
        Self { parent, name }
    }

    pub fn parent(self) -> Id {
        self.parent
    }

    pub fn name(self) -> Symbol {
        self.name
    }
}

impl FluxDefId {
    pub fn as_local(self) -> Option<FluxLocalDefId> {
        #[allow(
            clippy::disallowed_methods,
            reason = "we also have a warning for `FluxId::as_local`"
        )]
        Some(FluxId { parent: self.parent.as_local()?, name: self.name })
    }

    pub fn expect_local(self) -> FluxLocalDefId {
        #[allow(
            clippy::disallowed_methods,
            reason = "we also have a warning for `FluxId::expect_local`"
        )]
        FluxId { parent: self.parent.expect_local(), name: self.name }
    }

    pub fn index(self) -> FluxId<DefIndex> {
        FluxId { parent: self.parent.index, name: self.name }
    }
}

impl FluxLocalDefId {
    pub fn to_def_id(self) -> FluxDefId {
        FluxDefId { parent: self.parent.to_def_id(), name: self.name }
    }
}

impl FluxId<MaybeExternId> {
    pub fn local_id(self) -> FluxLocalDefId {
        FluxLocalDefId { parent: self.parent.local_id(), name: self.name }
    }
}

/// This enum serves as a type-level reminder that a local definition _may be_ a wrapper for an
/// extern spec. This abstraction is not infallible, so one should be careful and decide in each
/// situation whether to use the [_local id_] or the [_resolved id_].
///
/// The construction of [`MaybeExternId`] is not encapsulated, but it is recommended to use
/// [`GlobalEnv::maybe_extern_id`] to create one.
///
/// The enum is generic on the local `Id` as we use it with various kinds of local ids, e.g.,
/// [`LocalDefId`], [`OwnerId`], ...
///
/// [_local id_]: MaybeExternId::local_id
/// [_resolved id_]: MaybeExternId::resolved_id
/// [`GlobalEnv::maybe_extern_id`]: crate::global_env::GlobalEnv::maybe_extern_id
#[derive(Clone, Copy, Debug)]
pub enum MaybeExternId<Id = LocalDefId> {
    /// An id for a local spec.
    Local(Id),
    /// A "dummy" local definition wrapping an external spec. The `Id` is the local id of the definition
    /// corresponding to the extern spec. The `DefId` is the _resolved_ id for the external definition.
    Extern(Id, DefId),
}

impl<Id> MaybeExternId<Id> {
    pub fn map<R>(self, f: impl FnOnce(Id) -> R) -> MaybeExternId<R> {
        match self {
            MaybeExternId::Local(local_id) => MaybeExternId::Local(f(local_id)),
            MaybeExternId::Extern(local_id, def_id) => MaybeExternId::Extern(f(local_id), def_id),
        }
    }

    pub fn local_id(self) -> Id {
        match self {
            MaybeExternId::Local(local_id) | MaybeExternId::Extern(local_id, _) => local_id,
        }
    }

    #[track_caller]
    pub fn expect_local(self) -> Id {
        match self {
            MaybeExternId::Local(local_id) => local_id,
            MaybeExternId::Extern(..) => bug!("expected `MaybeExternId::Local`"),
        }
    }

    /// Returns `true` if the maybe extern id is [`Local`].
    ///
    /// [`Local`]: MaybeExternId::Local
    #[must_use]
    pub fn is_local(self) -> bool {
        matches!(self, Self::Local(..))
    }

    /// Returns `true` if the maybe extern id is [`Extern`].
    ///
    /// [`Extern`]: MaybeExternId::Extern
    #[must_use]
    pub fn is_extern(&self) -> bool {
        matches!(self, Self::Extern(..))
    }

    pub fn as_local(self) -> Option<Id> {
        if let MaybeExternId::Local(local_id) = self { Some(local_id) } else { None }
    }

    pub fn as_extern(self) -> Option<DefId> {
        if let MaybeExternId::Extern(_, def_id) = self { Some(def_id) } else { None }
    }
}

impl<Id: Into<DefId>> MaybeExternId<Id> {
    /// Returns the [`DefId`] this id _truly_ corresponds to, i.e, returns the [`DefId`] of the
    /// extern definition if [`Extern`] or converts the local id into a [`DefId`] if [`Local`].
    ///
    /// [`Local`]: MaybeExternId::Local
    /// [`Extern`]: MaybeExternId::Extern
    pub fn resolved_id(self) -> DefId {
        match self {
            MaybeExternId::Local(local_id) => local_id.into(),
            MaybeExternId::Extern(_, def_id) => def_id,
        }
    }
}

impl rustc_middle::query::IntoQueryParam<DefId> for MaybeExternId {
    fn into_query_param(self) -> DefId {
        self.resolved_id()
    }
}

/// Normally, a [`DefId`] is either local or external, and [`DefId::as_local`] can be used to
/// distinguish between the two. However, extern specs introduce a third case: a local definition
/// wrapping an extern spec. This enum is a type level reminder used to differentiate between these
/// three cases.
///
/// The construction of [`ResolvedDefId`] is not encapsulated, but it is recommended to use
/// [`GlobalEnv::resolve_id`] to create one.
///
/// This is used when we are given a [`DefId`] and we need to resolve it into one of these three
/// cases. For handling local items that may correspond to an extern spec, see [`MaybeExternId`].
#[derive(Clone, Copy)]
pub enum ResolvedDefId {
    /// A local definition. Corresponds to [`MaybeExternId::Local`].
    Local(LocalDefId),
    /// A "dummy" local definition wrapping an extern spec. The `LocalDefId` is for the local item,
    /// and the `DefId` is the resolved id for the external spec. Corresponds to
    /// [`MaybeExternId::Extern`].
    ExternSpec(LocalDefId, DefId),
    /// An external definition with no corresponding (local) extern spec.
    Extern(DefId),
}

impl ResolvedDefId {
    pub fn as_maybe_extern(self) -> Option<MaybeExternId> {
        match self {
            ResolvedDefId::Local(local_id) => Some(MaybeExternId::Local(local_id)),
            ResolvedDefId::ExternSpec(local_id, def_id) => {
                Some(MaybeExternId::Extern(local_id, def_id))
            }
            ResolvedDefId::Extern(_) => None,
        }
    }
}
