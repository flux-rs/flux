use super::ast::*;

macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}

pub trait MutVisitor: Sized {
    fn visit_fn_type(&mut self, fn_typ: &mut FnType) {
        walk_fn_type(self, fn_typ);
    }

    fn visit_refine(&mut self, refine: &mut Reft) {
        walk_refine(self, refine);
    }

    fn visit_expression(&mut self, expr: &mut Pred) {
        walk_expression(self, expr);
    }

    fn visit_name(&mut self, _: &mut Name) {}
}

pub fn walk_fn_type<V: MutVisitor>(vis: &mut V, fn_typ: &mut FnType) {
    walk_list!(vis, visit_refine, &mut fn_typ.inputs);
    walk_refine(vis, &mut fn_typ.output);
}

pub fn walk_refine<V: MutVisitor>(vis: &mut V, refine: &mut Reft) {
    vis.visit_expression(&mut refine.pred);
}

pub fn walk_expression<V: MutVisitor>(vis: &mut V, expr: &mut Pred) {
    match &mut expr.kind {
        ExprKind::Name(ident) => vis.visit_name(ident),
        ExprKind::Binary(e1, _, e2) => {
            vis.visit_expression(e1);
            vis.visit_expression(e2);
        }
        ExprKind::Unary(_, e) => walk_expression(vis, e),
        ExprKind::Lit(_) | ExprKind::Err => {}
    }
}
