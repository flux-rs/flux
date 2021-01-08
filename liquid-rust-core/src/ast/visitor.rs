use super::*;

pub trait Visitor<I, S = usize>: Sized {
    fn visit_fn_body(&mut self, fn_body: &FnBody<I, S>) {
        walk_fn_body(self, fn_body);
    }

    fn visit_statement(&mut self, stmnt: &Statement<I, S>) {
        walk_statement(self, stmnt);
    }

    fn visit_cont_def(&mut self, def: &ContDef<I, S>) {
        walk_cont_def(self, def);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<S>) {
        walk_rvalue(self, rvalue);
    }

    fn visit_operand(&mut self, operand: &Operand<S>) {
        walk_operand(self, operand);
    }

    fn visit_local(&mut self, _local: &Local<S>) {}

    fn visit_constant(&mut self, _constant: &Constant) {}

    fn visit_place(&mut self, _place: &Place<S>) {}

    fn visit_cont_id(&mut self, _const_id: &ContId<S>) {}
}

#[macro_export]
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
    ($visitor: expr, $method: ident, $list: expr, $($extra_args: expr),*) => {
        for elem in $list {
            $visitor.$method(elem, $($extra_args,)*)
        }
    }
}

pub fn walk_fn_body<I, S, V: Visitor<I, S>>(visitor: &mut V, fn_body: &FnBody<I, S>) {
    match fn_body {
        FnBody::LetCont(defs, rest) => {
            walk_list!(visitor, visit_cont_def, defs);
            visitor.visit_fn_body(rest);
        }
        FnBody::Ite { discr, then, else_ } => {
            visitor.visit_place(discr);
            visitor.visit_fn_body(then);
            visitor.visit_fn_body(else_);
        }
        FnBody::Call { func, args, ret } => {
            visitor.visit_place(func);
            walk_list!(visitor, visit_local, args);
            visitor.visit_cont_id(ret);
        }
        FnBody::Jump { target, args } => {
            visitor.visit_cont_id(target);
            walk_list!(visitor, visit_local, args);
        }
        FnBody::Seq(st, rest) => {
            visitor.visit_statement(st);
            visitor.visit_fn_body(rest);
        }
        FnBody::Abort => {}
    }
}

pub fn walk_cont_def<I, S, V: Visitor<I, S>>(visitor: &mut V, def: &ContDef<I, S>) {
    visitor.visit_fn_body(&def.body);
    visitor.visit_cont_id(&def.name);
    walk_list!(visitor, visit_local, &def.params);
}

pub fn walk_statement<I, S, V: Visitor<I, S>>(visitor: &mut V, stmnt: &Statement<I, S>) {
    match &stmnt.kind {
        StatementKind::Let(local, _) => {
            visitor.visit_local(local);
        }
        StatementKind::Assign(place, rvalue) => {
            visitor.visit_place(place);
            visitor.visit_rvalue(rvalue);
        }
        StatementKind::Drop(local) => {
            visitor.visit_local(local);
        }
    }
}

pub fn walk_rvalue<I, S, V: Visitor<I, S>>(visitor: &mut V, rvalue: &Rvalue<S>) {
    match rvalue {
        Rvalue::Use(operand) => {
            visitor.visit_operand(operand);
        }
        Rvalue::Ref(_, place) => {
            visitor.visit_place(place);
        }
        Rvalue::CheckedBinaryOp(_, lhs, rhs) | Rvalue::BinaryOp(_, lhs, rhs) => {
            visitor.visit_operand(lhs);
            visitor.visit_operand(rhs);
        }
        Rvalue::UnaryOp(_, operand) => {
            visitor.visit_operand(operand);
        }
    }
}

pub fn walk_operand<I, S, V: Visitor<I, S>>(visitor: &mut V, operand: &Operand<S>) {
    match operand {
        Operand::Use(place) => visitor.visit_place(place),
        Operand::Constant(c) => visitor.visit_constant(c),
    }
}
