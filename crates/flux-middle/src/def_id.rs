use flux_common::bug;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, LocalDefId};
use rustc_macros::{Decodable, Encodable};
use rustc_span::{Span, Symbol};

/// An id for a Flux-specific item that doesn't have a corresponding Rust item and thus, we cannot
/// identify it with a [`DefId`]. This includes, for example, associated refinements, qualifiers
/// and refinement functions.
///
/// # Type-level invariant
/// This struct maintains a type-level invariant ensuring that the referenced item exists. The id is
/// composed of two parts:
/// * `parent`: A reference to a parent Rust item
/// * `name`: A name uniquely identifiying the item within the parent
///
/// Since the name can be an arbitrary [`Symbol`], this doesn't guarantee the existence of the item,
/// so we must be careful when creating instances of this struct.
///
/// # Implementation Details
/// * Fields are private to ensure construction only through [`FluxId::new`]
/// * A clippy lint prevents direct usage of [`FluxId::new`], which can be selectively disabled
///   when item existence is guaranteed
/// * The type is parametric over the parent `Id` type to support various id types (e.g., [`DefId`],
///   [`MaybeExternId`])
#[derive(Debug, Copy, Clone, Encodable, Decodable)]
pub struct FluxId<Id> {
    parent: Id,
    name: Symbol,
    span: Span,
}

// Exclude span from equality comparison
impl<Id: PartialEq> PartialEq for FluxId<Id> {
    fn eq(&self, other: &Self) -> bool {
        self.parent == other.parent && self.name == other.name
    }
}

impl<Id: Eq> Eq for FluxId<Id> {}

// Exclude span from hash computation to match equality
impl<Id: std::hash::Hash> std::hash::Hash for FluxId<Id> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.parent.hash(state);
        self.name.hash(state);
    }
}

pub type FluxDefId = FluxId<DefId>;
pub type FluxLocalDefId = FluxId<LocalDefId>;

impl<Id> FluxId<Id> {
    pub fn new(parent: Id, name: Symbol, span: Span) -> Self {
        Self { parent, name, span }
    }

    pub fn parent(self) -> Id {
        self.parent
    }

    pub fn name(self) -> Symbol {
        self.name
    }

    pub fn span(self) -> Span {
        self.span
    }
}

impl FluxDefId {
    pub fn as_local(self) -> Option<FluxLocalDefId> {
        #[allow(
            clippy::disallowed_methods,
            reason = "we also have a warning for `FluxId::as_local`"
        )]
        Some(FluxId { parent: self.parent.as_local()?, name: self.name, span: self.span })
    }

    #[track_caller]
    pub fn expect_local(self) -> FluxLocalDefId {
        #[allow(
            clippy::disallowed_methods,
            reason = "we also have a warning for `FluxId::expect_local`"
        )]
        match self.as_local() {
            Some(local_id) => local_id,
            None => panic!("FluxDefId::expect_local: `{self:?}` isn't local"),
        }
    }

    pub fn krate(self) -> CrateNum {
        self.parent.krate
    }

    pub fn index(self) -> FluxId<DefIndex> {
        FluxId { parent: self.parent.index, name: self.name, span: self.span }
    }
}

impl FluxLocalDefId {
    pub fn to_def_id(self) -> FluxDefId {
        FluxDefId { parent: self.parent.to_def_id(), name: self.name, span: self.span }
    }

    pub fn local_def_index(self) -> FluxId<DefIndex> {
        FluxId { parent: self.parent.local_def_index, name: self.name, span: self.span }
    }
}

impl FluxId<MaybeExternId> {
    pub fn local_id(self) -> FluxLocalDefId {
        FluxLocalDefId { parent: self.parent.local_id(), name: self.name, span: self.span }
    }
}

impl rustc_middle::query::IntoQueryParam<FluxDefId> for FluxLocalDefId {
    fn into_query_param(self) -> FluxDefId {
        self.to_def_id()
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
/// [`LocalDefId`], [`DefId`], ...
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
///
/// [`GlobalEnv::resolve_id`]: crate::global_env::GlobalEnv::resolve_id
#[derive(Clone, Copy, Debug)]
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
