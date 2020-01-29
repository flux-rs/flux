use super::ast::*;

macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}

pub trait MutVisitor<'ast>: Sized {
    fn visit_fn_type(&mut self, fn_typ: &mut FnType) {
        walk_fn_type(self, fn_typ);
    }

    fn visit_refine(&mut self, refine: &mut Refine) {
        walk_refine(self, refine);
    }

    fn visit_expression(&mut self, expr: &mut Expr) {
        walk_expression(self, expr);
    }

    fn visit_ident(&mut self, _: &mut Ident) {}
}

pub fn walk_fn_type<'ast, V: MutVisitor<'ast>>(vis: &mut V, fn_typ: &mut FnType) {
    walk_list!(vis, visit_refine, &mut fn_typ.inputs);
    walk_refine(vis, &mut fn_typ.output);
}

pub fn walk_refine<'ast, V: MutVisitor<'ast>>(vis: &mut V, refine: &mut Refine) {
    vis.visit_ident(&mut refine.binding);
    vis.visit_expression(&mut refine.pred);
}

pub fn walk_expression<'ast, V: MutVisitor<'ast>>(vis: &mut V, expr: &mut Expr) {
    match &mut expr.kind {
        ExprKind::Ident(ident) => vis.visit_ident(ident),
        ExprKind::Binary(e1, _, e2) => {
            walk_expression(vis, e1);
            walk_expression(vis, e2);
        }
        ExprKind::Unary(_, e) => walk_expression(vis, e),
        ExprKind::True | ExprKind::False | ExprKind::Int(_) => {}
    }
}
