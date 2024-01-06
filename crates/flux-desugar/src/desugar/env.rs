use std::fmt;

use flux_errors::FluxSession;
use flux_syntax::surface::{Ident, NodeId};
use rustc_data_structures::fx::{FxIndexMap, IndexEntry};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::ErrorGuaranteed;

use super::errors::DuplicateParam;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

/// The environment used for desugaring that tracks parameter names and shadowing. An environment
/// is a tree formed by nested scopes.
pub(crate) struct Env<P> {
    scopes: FxHashMap<ScopeId, Scope<P>>,
    parent: FxHashMap<ScopeId, ScopeId>,
    children: FxHashMap<ScopeId, FxHashSet<ScopeId>>,
    root: ScopeId,
    curr: ScopeId,
}

impl<P> Env<P> {
    pub(crate) fn new(root: ScopeId) -> Self {
        let mut scopes = FxHashMap::default();
        scopes.insert(root, Scope::new());
        Self { scopes, parent: Default::default(), children: Default::default(), root, curr: root }
    }

    /// Inserts a parameter in the current scope, returning an error if a parameter with the
    /// same name is already in the scope.
    pub(crate) fn insert(&mut self, sess: &FluxSession, ident: Ident, param: P) -> Result {
        self.curr().insert(sess, ident, param)
    }

    /// Extends the current scope with a list of parameters reporting an error if there are any
    /// dupliates.
    pub(crate) fn extend(
        &mut self,
        sess: &FluxSession,
        params: impl IntoIterator<Item = (Ident, P)>,
    ) -> Result {
        self.curr().extend(sess, params)
    }

    pub(crate) fn get(&self, ident: Ident) -> Option<&P> {
        self.find_map(|_, scope| scope.map.get(&ident))
    }

    pub(crate) fn get_with_scope(&self, ident: Ident) -> Option<(ScopeId, &P)> {
        self.find_map(|id, scope| scope.map.get(&ident).map(|param| (id, param)))
    }

    fn find_map<'a, T>(
        &'a self,
        mut f: impl FnMut(ScopeId, &'a Scope<P>) -> Option<T>,
    ) -> Option<T> {
        let mut curr = self.curr;
        loop {
            let scope = self.scopes.get(&curr).unwrap();
            if let Some(res) = f(curr, scope) {
                return Some(res);
            }
            if let Some(parent) = self.parent.get(&curr) {
                curr = *parent;
            } else {
                return None;
            }
        }
    }

    pub(crate) fn scope(&mut self, id: ScopeId) -> &mut Scope<P> {
        self.scopes.get_mut(&id).unwrap()
    }

    /// Push a scope with `id` as a child of the current scope and then enters the new scope.
    /// The `id` must be different from any scope already in the environment.
    ///
    /// # Panics
    ///
    /// Panics if `id` is already in the enrvionment
    pub(crate) fn push(&mut self, id: ScopeId) {
        assert!(self.scopes.insert(id, Scope::new()).is_none());
        self.children.entry(self.curr).or_default().insert(id);
        self.parent.insert(id, self.curr);
        self.curr = id;
    }

    /// Remove the current scope and return it. Then set the current scope to the parent scope.
    ///
    /// # Panics
    ///
    /// Panics if the current scope has children.
    pub(crate) fn pop(&mut self) -> Scope<P> {
        let children = self.children.remove(&self.curr).unwrap_or_default();
        if !children.is_empty() {
            panic!("cannot pop scope with children");
        }
        let id = self.curr;
        let parent = self.parent.remove(&id).unwrap();
        self.children.entry(parent).or_default().remove(&id);
        self.curr = parent;
        self.scopes.remove(&id).unwrap()
    }

    /// Enter a child scope.
    ///
    /// # Panics
    ///
    /// Panics if `scope` is not a child of the current scope.
    #[track_caller]
    pub(crate) fn enter(&mut self, scope: ScopeId) {
        if self.curr != self.parent[&scope] {
            panic!("{scope:?} is not a children of the current scope");
        }
        self.curr = scope;
    }

    /// Exit the current scope back into the parent scope.
    ///
    /// # Panics
    ///
    /// Panics if the current scope is the root scope.
    #[track_caller]
    pub(crate) fn exit(&mut self) {
        self.curr = self.parent[&self.curr];
    }

    pub(crate) fn filter_map<T>(self, mut f: impl FnMut(P, bool) -> Option<T>) -> Env<T> {
        let scopes = self
            .scopes
            .into_iter()
            .map(|(id, mut scope)| {
                let map = scope
                    .map
                    .into_iter()
                    .flat_map(|(ident, param)| {
                        if let Some(r) = f(param, scope.used.contains(&ident)) {
                            Some((ident, r))
                        } else {
                            scope.used.remove(&ident);
                            None
                        }
                    })
                    .collect();
                (id, Scope { map, used: scope.used })
            })
            .collect();
        Env {
            scopes,
            parent: self.parent,
            children: self.children,
            root: self.root,
            curr: self.root,
        }
    }

    fn curr(&mut self) -> &mut Scope<P> {
        self.scopes.get_mut(&self.curr).unwrap()
    }

    pub(crate) fn root(&mut self) -> &mut Scope<P> {
        self.scopes.get_mut(&self.root).unwrap()
    }

    pub(crate) fn into_root(mut self) -> Scope<P> {
        assert!(self.curr == self.root);
        self.scopes.remove(&self.root).unwrap()
    }
}

impl<P: fmt::Debug> Env<P> {
    fn fmt_rec(
        &self,
        scope_id: ScopeId,
        prefix: &str,
        is_last: bool,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let is_root = scope_id == self.root;
        let scope = self.scopes.get(&scope_id).unwrap();
        let node_str = if is_root {
            ""
        } else if is_last {
            "└── "
        } else {
            "├── "
        };
        writeln!(f, "{}{}{:?} {:?}", prefix, node_str, scope_id, scope.map)?;

        let Some(children) = self.children.get(&scope_id) else {
            return Ok(());
        };

        let new_prefix = format!(
            "{}{}",
            prefix,
            if is_root {
                ""
            } else if is_last {
                "    "
            } else {
                "│   "
            }
        );

        for (i, child) in children.iter().enumerate() {
            let is_last_child = i == children.len() - 1;
            self.fmt_rec(*child, &new_prefix, is_last_child, f)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub(crate) struct Scope<P> {
    map: FxIndexMap<Ident, P>,
    used: FxHashSet<Ident>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) enum ScopeId {
    /// The scope introduced by a function's input parameters. It contains explicit parameters plus
    /// synthetic parameters declared with `@x` or `x: T`.
    FnInput(NodeId),
    /// The scope introduced by a function's output parameters. It contains synthetic parameters
    /// declared with `#n` syntax.
    FnOutput(NodeId),
    /// The scope introduced by the `refined_by` annotation in a struct.
    Struct(NodeId),
    /// The scope introduced by the `refined_by` annotation in a struct. This scope is not relevant
    /// for variants, but only for the invariants of the type.
    Enum(NodeId),
    /// The scope introduced by variant. It includes parameters introduced with `@n` syntax.
    Variant(NodeId),
    /// The scope introduced by type alias. It includes the early bound and index parameters.
    TyAlias(NodeId),
    /// The scope introduced by lambda abstraction. It includes the parameters of the lambda.
    Abs(NodeId),
    /// The scope introduced by an existential type. Either the shorthand syntax or the general syntax.
    Exists(NodeId),
    /// The scope introduced by a flux item like a func definition or a qualifier. It includes
    /// parameters of the item
    FluxItem,
}

impl<P> Scope<P> {
    fn new() -> Self {
        Self { map: Default::default(), used: Default::default() }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Ident, &P)> {
        self.map.iter()
    }

    pub(crate) fn into_iter(self) -> impl Iterator<Item = (Ident, P)> {
        self.map.into_iter()
    }

    pub(crate) fn mark_as_used(&mut self, ident: Ident) {
        let (key, _) = self.map.get_key_value(&ident).unwrap();
        self.used.insert(*key);
    }

    fn insert(&mut self, sess: &FluxSession, ident: Ident, param: P) -> Result {
        match self.map.entry(ident) {
            IndexEntry::Occupied(entry) => {
                Err(sess.emit_err(DuplicateParam::new(*entry.key(), ident)))
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(param);
                Ok(())
            }
        }
    }

    fn extend(
        &mut self,
        sess: &FluxSession,
        params: impl IntoIterator<Item = (Ident, P)>,
    ) -> Result {
        for (ident, param) in params {
            self.insert(sess, ident, param)?;
        }
        Ok(())
    }
}

impl<P: fmt::Debug> fmt::Debug for Env<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_rec(self.root, "", true, f)
    }
}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScopeId::FnInput(node_id) => write!(f, "FnInput({})", node_id.as_usize()),
            ScopeId::FnOutput(node_id) => write!(f, "FnOutput({})", node_id.as_usize()),
            ScopeId::Struct(node_id) => write!(f, "Struct({})", node_id.as_usize()),
            ScopeId::Enum(node_id) => write!(f, "Enum({})", node_id.as_usize()),
            ScopeId::Variant(node_id) => write!(f, "Variant({})", node_id.as_usize()),
            ScopeId::TyAlias(node_id) => write!(f, "TyAlias({})", node_id.as_usize()),
            ScopeId::Abs(node_id) => write!(f, "Abs({})", node_id.as_usize()),
            ScopeId::Exists(node_id) => write!(f, "Exists({})", node_id.as_usize()),
            ScopeId::FluxItem => write!(f, "FluxItem"),
        }
    }
}
