use super::ast::*;

macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr) => {
        for elem in $list {
            $visitor.$method(elem)
        }
    };
}

pub trait Visitor: Sized {
    fn visit_fn_type(&mut self, fn_typ: &FnType) {
        walk_fn_type(self, fn_typ);
    }

    fn visit_refine(&mut self, refine: &Reft) {
        walk_refine(self, refine);
    }

    fn visit_expression(&mut self, expr: &Pred) {
        walk_expression(self, expr);
    }

    fn visit_name(&mut self, _: &Name) {}
}

pub fn walk_fn_type<V: Visitor>(vis: &mut V, fn_typ: &FnType) {
    walk_list!(vis, visit_refine, &fn_typ.inputs);
    walk_refine(vis, &fn_typ.output);
}

pub fn walk_refine<V: Visitor>(vis: &mut V, refine: &Reft) {
    vis.visit_expression(&refine.pred);
}

pub fn walk_expression<V: Visitor>(vis: &mut V, expr: &Pred) {
    match &expr.kind {
        ExprKind::Name(ident) => vis.visit_name(ident),
        ExprKind::Binary(e1, _, e2) => {
            vis.visit_expression(e1);
            vis.visit_expression(e2);
        }
        ExprKind::Unary(_, e) => vis.visit_expression(e),
        ExprKind::Lit(_) | ExprKind::Err => {}
    }
}
