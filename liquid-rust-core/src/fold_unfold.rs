use crate::ir::{
    BasicBlockData, Body, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};

pub fn add_fold_unfold(body: Body) -> Body {
    Body {
        basic_blocks: body
            .basic_blocks
            .into_iter()
            .map(add_fold_unfold_bb)
            .collect(),
        ..body
    }
}

fn add_fold_unfold_bb(data: BasicBlockData) -> BasicBlockData {
    let statements: Vec<_> = data
        .statements
        .into_iter()
        .flat_map(add_fold_unfold_stmt)
        .chain(add_fold_unfold_terminator(&data.terminator))
        .collect();

    BasicBlockData { statements, terminator: data.terminator }
}

fn add_fold_unfold_terminator(terminator: &Option<Terminator>) -> Vec<Statement> {
    if let Some(terminator) = terminator {
        let mut places = vec![];
        gather_places_terminator(terminator, &mut places);
        places
            .into_iter()
            .map(|place| {
                let kind = match &place.projection[..] {
                    [] | [PlaceElem::Deref] => StatementKind::Fold(Place::new(place.local, vec![])),
                    [PlaceElem::Field(_)] => StatementKind::Unfold(Place::new(place.local, vec![])),
                    _ => todo!(""),
                };
                Statement { kind, source_info: terminator.source_info }
            })
            .collect()
    } else {
        vec![]
    }
}

fn add_fold_unfold_stmt(stmt: Statement) -> Vec<Statement> {
    let mut stmts = vec![];
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            let mut places = vec![place];
            gather_places_rvalue(rvalue, &mut places);
            stmts.extend(places.into_iter().map(|place| {
                let kind = match &place.projection[..] {
                    [] | [PlaceElem::Deref] => StatementKind::Fold(Place::new(place.local, vec![])),
                    [PlaceElem::Field(_)] => StatementKind::Unfold(Place::new(place.local, vec![])),
                    _ => todo!(""),
                };
                Statement { kind, source_info: stmt.source_info }
            }));
        }
        StatementKind::Fold(_) | StatementKind::Unfold(_) | StatementKind::Nop => {}
    }
    stmts.push(stmt);
    stmts
}

fn gather_places_terminator<'a>(terminator: &'a Terminator, places: &mut Vec<&'a Place>) {
    match &terminator.kind {
        TerminatorKind::Call { args, destination, .. } => {
            for op in args {
                gather_places_operand(op, places);
            }
            if let Some((place, _)) = destination {
                places.push(place);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => gather_places_operand(discr, places),
        TerminatorKind::Drop { place, .. } => places.push(place),
        TerminatorKind::Assert { cond, .. } => gather_places_operand(cond, places),
        TerminatorKind::Goto { .. } | TerminatorKind::Return => {}
    }
}

fn gather_places_rvalue<'a>(rvalue: &'a Rvalue, places: &mut Vec<&'a Place>) {
    match rvalue {
        Rvalue::Use(op) => gather_places_operand(op, places),
        Rvalue::MutRef(place) | Rvalue::ShrRef(place) => {
            places.push(place);
        }
        Rvalue::BinaryOp(_, op1, op2) => {
            gather_places_operand(op1, places);
            gather_places_operand(op2, places);
        }
        Rvalue::UnaryOp(_, op) => gather_places_operand(op, places),
    }
}

fn gather_places_operand<'a>(op: &'a Operand, places: &mut Vec<&'a Place>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => places.push(place),
        Operand::Constant(_) => {}
    }
}
