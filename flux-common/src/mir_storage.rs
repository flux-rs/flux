/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! This module allows storing mir bodies with borrowck facts in a thread-local
//! storage. Unfortunately, thread local storage requires all data stored in it
//! to have a `'static` lifetime. Therefore, we transmute the lifetime `'tcx`
//! away when storing the data. To ensure that nothing gets meessed up, we
//! require the client to provide a witness: an instance of type `TyCtxt<'tcx>`
//! that is used to show that the lifetime that the client provided is indeed
//! `'tcx`.

use std::{cell::RefCell, collections::HashMap, thread_local};

use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Body, ty::TyCtxt};

thread_local! {
    pub static SHARED_STATE:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

/// # Safety
///
/// See the module level comment.
pub unsafe fn store_mir_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body_with_facts: BodyWithBorrowckFacts<'tcx>,
) {
    // SAFETY: See the module level comment.
    let body_with_facts: BodyWithBorrowckFacts<'static> = std::mem::transmute(body_with_facts);
    SHARED_STATE.with(|state| {
        let mut map = state.borrow_mut();
        assert!(map.insert(def_id, body_with_facts).is_none());
    });
}

/// # Safety
///
/// See the module level comment.
#[allow(clippy::needless_lifetimes)] // We want to be very explicit about lifetimes here.
pub unsafe fn retrieve_mir_body<'tcx>(_tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Body<'tcx> {
    let body_with_facts: Body<'static> = SHARED_STATE.with(|state| {
        match state.borrow().get(&def_id) {
            Some(r) => r.body.clone(),
            None => panic!("retrieve_mir_body: panic on {def_id:?}"),
        }
    });
    // SAFETY: See the module level comment.
    std::mem::transmute(body_with_facts)
}
