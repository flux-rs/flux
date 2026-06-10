<img
    src="assets/logo-wide.svg"
    alt="flux logo" class="flux-logo">

Flux is a refinement type checker for Rust.

# Help and Discussions

If you need help using Flux or would like to discuss, you can post on the discussions forum or join
our [Zulip chat](https://flux-rs.zulipchat.com/)!

# Online Demo

You can try Flux [online at this site](https://flux.goto.ucsd.edu/).

# Overview

For an overview, take a look at the [Flux website](https://flux-rs.github.io).

# Docs

Documentation, including installation and usage guides can be found on the
[website](https://flux-rs.github.io/flux).

# Sponsors

### [![Zulip logo](https://static.zulipchat.com/static/images/logo/zulip-icon-128x128.png)](https://zulip.com)

**[Zulip](https://zulip.com)** — Zulip Cloud Standard generously provided free of charge.

fn no*ghosts_at<'ck, 'tcx>(
checker_id: CheckerId,
ghost_stmts: &'ck UnordMap<CheckerId, GhostStatements>,
body: &'ck Body<'tcx>,
src_bb: BasicBlock,
dst_bb: BasicBlock,
) -> bool {
let Some(ghosts) = ghost_stmts.get(&checker_id) else {
return true;
};
let mut no_before = true;
let mut location = Location { block: dst_bb, statement_index: 0 };
for * in &body.basic_blocks[dst_bb].statements {
no_before = no_before
&& ghosts
.statements_at(Point::BeforeLocation(location))
.next()
.is_none();
location = location.successor_within_block();
// self.check_ghost_statements_at(
// &mut infcx,
// &mut env,
// Point::BeforeLocation(location),
// span,
// )?;
}
no_before = no_before
&& ghosts
.statements_at(Point::BeforeLocation(location))
.next()
.is_none();
// self.check_ghost_statements_at(&mut infcx, &mut env, Point::BeforeLocation(location), span)?;

    // CLAUDE
    // let num_stmts = body.basic_blocks[src_bb].statements.len();
    // let no_before = (0..=num_stmts).all(|i| {
    //     let loc = Location { block: src_bb, statement_index: i };
    //     ghosts
    //         .statements_at(Point::BeforeLocation(loc))
    //         .next()
    //         .is_none()
    // });
    let no_edge = ghosts
        .statements_at(Point::Edge(src_bb, dst_bb))
        .next()
        .is_none();
    no_before && no_edge

}

fn terminator_for<'ck, 'tcx>(
checker_id: CheckerId,
ghost_stmts: &'ck UnordMap<CheckerId, GhostStatements>,
body: &'ck Body<'tcx>,
src_bb: BasicBlock,
) -> Option<&'ck Terminator<'tcx>> {
let bb_term = &body.basic_blocks[src_bb].terminator;
let Some(terminator) = bb_term else {
return None;
};
if let TerminatorKind::Goto { target: dst_bb } = &terminator.kind
&& body.is_dummy_basic_block(*dst_bb).is_some()
&& no_ghosts_at(checker_id, ghost_stmts, body, src_bb, *dst_bb)
{
println!("TRACE: skipping terminator from {src_bb:?} ==> {dst_bb:?}");
terminator_for(checker_id, ghost_stmts, body, \*dst_bb)
} else {
bb_term.as_ref()
}
}
