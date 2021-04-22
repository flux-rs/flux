use super::*;
use liquid_rust_lrir::ty::{BinOp, BorrowKind, Pred, PredKind, PredS, TyS};
use std::{
    collections::HashSet,
    io::{self, Write},
};

/// Writes out a mapping from locals directly to the type of the corresponding
/// GhostVar.
pub fn write_env(l: &LocalEnv, w: &mut dyn Write) -> io::Result<()> {
    write!(w, "env: [")?;

    let mut seen = HashSet::new();

    for frame in &l.locals {
        for (local, gv) in frame.iter() {
            // If we haven't seen the local yet...
            if seen.insert(local) {
                // We get the corresponding type from the binding tree
                let ty = l.bindings.lookup(gv);
                // And write out the binding from the local to the ghost var
                write!(w, "  {:?} => ", local)?;
                write_ty(l, w, ty)?;
                writeln!(w)?;
            }
        }
    }

    writeln!(w, "]")?;

    Ok(())
}

// These formatting functions are basically just copied over from the Display
// implementations of refinement types; the only difference is for Vars, we
// try to match ghost variables to their corresponding locals in the
// environment first.
fn write_ty(l: &LocalEnv, w: &mut dyn Write, t: &TyS) -> io::Result<()> {
    match t.kind() {
        TyKind::Ref(BorrowKind::Shared, r, gv) => {
            write!(w, "&{} ", r)?;
            lookup_gv(l, w, *gv)
        }
        TyKind::Ref(BorrowKind::Mut, r, gv) => {
            write!(w, "&{} mut ", r)?;
            lookup_gv(l, w, *gv)
        }
        TyKind::Tuple(tup) => {
            write!(w, "(")?;
            for (i, (f, ty)) in tup.iter().enumerate() {
                write!(w, "{}: ", f)?;
                write_ty(l, w, ty)?;
                if i != 0 {
                    write!(w, ", ")?;
                }
            }
            write!(w, ")")
        }
        TyKind::Uninit(size) => write!(w, "uninit({})", size),
        TyKind::Refined(bty, Refine::Infer(k)) => write!(w, "{{ {} | {} }}", bty, k),
        TyKind::Refined(bty, Refine::Pred(pred)) => {
            if pred.is_true() {
                write!(w, "{}", bty)
            } else {
                write!(w, "{{ {} | ", bty)?;
                write_pred(l, w, pred)?;
                write!(w, " }}")
            }
        }
    }
}

// fn write_refine(l: &LocalEnv, w: &mut dyn Write, r: &Refine) -> io::Result<()> {
//     match r {
//         Refine::Pred(pred) => write_pred(l, w, pred),
//         Refine::Infer(kvar) => write!(w, "{}", kvar),
//     }
// }

fn write_pred(l: &LocalEnv, w: &mut dyn Write, p: &PredS) -> io::Result<()> {
    fn should_parenthesize(bin_op: BinOp, child: &Pred) -> bool {
        if let PredKind::BinaryOp(child_op, ..) = child.kind() {
            child_op.precedence() < bin_op.precedence()
                || (child_op.precedence() == bin_op.precedence()
                    && !BinOp::associative(bin_op.precedence()))
        } else {
            false
        }
    }

    match p.kind() {
        PredKind::Path(path) => write_path(l, w, path)?,
        PredKind::BinaryOp(bin_op, op1, op2) => {
            if should_parenthesize(*bin_op, op1) {
                write!(w, "(")?;
                write_pred(l, w, op1)?;
                write!(w, ")")?;
            } else {
                write_pred(l, w, op1)?;
            }
            write!(w, " {} ", bin_op)?;
            if should_parenthesize(*bin_op, op2) {
                write!(w, "(")?;
                write_pred(l, w, op2)?;
                write!(w, ")")?;
            } else {
                write_pred(l, w, op2)?;
            }
        }
        PredKind::UnaryOp(un_op, op) => {
            if matches!(op.kind(), PredKind::Path(..) | PredKind::Const(..)) {
                write!(w, "{}", un_op)?;
                write_pred(l, w, op)?;
            } else {
                write!(w, "{}(", un_op)?;
                write_pred(l, w, op)?;
                write!(w, ")")?;
            }
        }
        PredKind::Const(c) => write!(w, "{}", c)?,
    }
    Ok(())
}

fn write_path(l: &LocalEnv, w: &mut dyn Write, v: &Path) -> io::Result<()> {
    write_var(l, w, &v.var)?;
    for proj in &v.projection {
        write!(w, ".{}", proj)?;
    }
    Ok(())
}

fn write_var(l: &LocalEnv, w: &mut dyn Write, v: &Var) -> io::Result<()> {
    match v {
        Var::Nu => write!(w, "v"),
        Var::Ghost(gv) => lookup_gv(l, w, *gv),
        Var::Field(fld) => write!(w, "{}", fld),
    }
}

// TODO: just return Option<Local>?
/// Attempts to find the local which maps to this ghost variable. If found, write
/// the local out instead of the ghost variable. Otherwise, just write the ghost
/// var out.
fn lookup_gv(l: &LocalEnv, w: &mut dyn Write, gv: GhostVar) -> io::Result<()> {
    // We basically have to iterate through everything to get to this point.
    let mut seen = HashSet::new();

    for frame in &l.locals {
        for (local, lgv) in frame.iter() {
            // If the local is bound to a ghost var at the top level (i.e. not a
            // shadowed definition):
            if seen.insert(local) && *lgv == gv {
                // Write the local!
                return write!(w, "{:?}", local);
            }
        }
    }

    return write!(w, "{}", gv);
}

// /// Writes a simplified version of the binding tree, removing ghost vars which
// /// are never used or referenced.
// pub fn write_simple_heap(l: &LocalEnv, w: &mut dyn Write) -> io::Result<()> {
//    todo!()
// }
