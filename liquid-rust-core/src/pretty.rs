use crate::{ast, names::*};
use std::fmt;

macro_rules! indent {
    ($formatter:expr, $indent:expr) => {
        ::std::write!($formatter, "\n{:>1$}", "", $indent)
    };
}

impl<I, S: Pretty> fmt::Display for ast::FnBody<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_fn_body(self, f, 0)
    }
}

impl<I, S: Pretty> fmt::Display for ast::Statement<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_statement(self, f)
    }
}

impl<S: Pretty> fmt::Display for ast::Operand<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_operand(self, f)
    }
}

impl<S: Pretty> fmt::Display for ast::Rvalue<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_rvalue(self, f)
    }
}

impl<S: Pretty> fmt::Display for ast::Ty<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_ty(self, f)
    }
}

pub struct PrettyPrinter;

impl PrettyPrinter {
    fn print_fn_body<I, S: Pretty>(
        &mut self,
        fn_body: &ast::FnBody<I, S>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        indent!(f, indent)?;
        match fn_body {
            ast::FnBody::LetCont(defs, rest) => {
                write!(f, "let ")?;
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        indent!(f, indent)?;
                        write!(f, "and ")?;
                    }
                    self.print_cont_def(def, f, indent + 2)?;
                }
                indent!(f, indent)?;
                write!(f, "in")?;
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Ite { discr, then, else_ } => {
                write!(f, "if ")?;
                self.print_place(discr, f)?;
                write!(f, " then")?;
                self.print_fn_body(then, f, indent + 2)?;
                indent!(f, indent)?;
                write!(f, "else")?;
                self.print_fn_body(else_, f, indent + 2)?;
            }
            ast::FnBody::Call { .. } => todo!(),
            ast::FnBody::Jump { target, args } => {
                write!(f, "jump ")?;
                self.print_cont_id(target, f)?;
                write!(f, "(")?;
                for (i, x) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    self.print_local(x, f)?;
                }
                write!(f, ")")?;
            }
            ast::FnBody::Seq(stmnt, rest) => {
                self.print_statement(stmnt, f)?;
                write!(f, ";")?;
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Abort => {
                write!(f, "abort")?;
            }
        }
        Ok(())
    }

    fn print_statement<I, S: Pretty>(
        &mut self,
        stmnt: &ast::Statement<I, S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match &stmnt.kind {
            ast::StatementKind::Let(x, layout) => {
                self.print_local(x, f)?;
                write!(f, " = alloc(")?;
                self.print_type_layout(layout, f)?;
                write!(f, ")")?;
            }
            ast::StatementKind::Assign(place, rvalue) => {
                self.print_place(place, f)?;
                write!(f, " = ")?;
                self.print_rvalue(rvalue, f)?;
            }
            ast::StatementKind::Drop(x) => {
                write!(f, "drop(")?;
                self.print_local(x, f)?;
                write!(f, ")")?;
            }
        };
        Ok(())
    }

    fn print_rvalue<S: Pretty>(
        &mut self,
        rvalue: &ast::Rvalue<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match rvalue {
            ast::Rvalue::Use(op) => {
                self.print_operand(op, f)?;
            }
            ast::Rvalue::Ref(bk, place) => {
                let bk = match bk {
                    ast::BorrowKind::Shared => "",
                    ast::BorrowKind::Mut => "mut",
                };
                write!(f, "&{} ", bk)?;
                self.print_place(place, f)?;
            }
            ast::Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.print_operand(op1, f)?;
                write!(f, " ")?;
                self.print_bin_op(bin_op, f)?;
                write!(f, " ")?;
                self.print_operand(op2, f)?;
            }
            ast::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                write!(f, "Checked(")?;
                self.print_operand(op1, f)?;
                write!(f, " ")?;
                self.print_bin_op(bin_op, f)?;
                write!(f, " ")?;
                self.print_operand(op2, f)?;
                write!(f, ")")?;
            }
            ast::Rvalue::UnaryOp(un_op, op) => {
                match un_op {
                    ast::UnOp::Not => {
                        write!(f, "¬")?;
                    }
                }
                self.print_operand(op, f)?;
            }
        };
        Ok(())
    }

    fn print_bin_op(&mut self, bin_op: &ast::BinOp, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match bin_op {
            ast::BinOp::Add => write!(f, "+"),
            ast::BinOp::Sub => write!(f, "-"),
            ast::BinOp::Lt => write!(f, "<"),
            ast::BinOp::Le => write!(f, "<="),
            ast::BinOp::Eq => write!(f, "="),
            ast::BinOp::Ge => write!(f, ">="),
            ast::BinOp::Gt => write!(f, ">"),
        }
    }

    fn print_operand<S: Pretty>(
        &mut self,
        op: &ast::Operand<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match op {
            ast::Operand::Use(place) => self.print_place(place, f),
            ast::Operand::Constant(c) => self.print_constant(c, f),
        }
    }

    fn print_constant(&mut self, c: &ast::Constant, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match c {
            ast::Constant::Bool(b) => write!(f, "{}", b),
            ast::Constant::Int(n) => write!(f, "{}", n),
            ast::Constant::Unit => write!(f, "()"),
        }
    }

    fn print_cont_def<I, S: Pretty>(
        &mut self,
        def: &ast::ContDef<I, S>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        self.print_cont_id(&def.name, f)?;
        indent!(f, indent + 2)?;
        write!(f, "( ")?;
        self.print_heap(&def.ty.heap, f)?;
        indent!(f, indent + 2)?;
        write!(f, "; ")?;
        self.print_locals(def.ty.locals.iter().map(|(x, l)| (x, l)), f)?;
        indent!(f, indent + 2)?;
        write!(f, "; ")?;
        self.print_locals(def.params.iter().zip(&def.ty.inputs), f)?;
        indent!(f, indent + 2)?;
        write!(f, ") =")?;
        self.print_fn_body(&def.body, f, indent)?;
        Ok(())
    }

    fn print_locals<'a, S: Pretty + 'a, I: IntoIterator<Item = (&'a Local<S>, &'a Location<S>)>>(
        &mut self,
        params: I,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        for (i, (x, l)) in params.into_iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            self.print_local(x, f)?;
            write!(f, ": own(")?;
            self.print_location(l, f)?;
            write!(f, ")")?;
        }
        Ok(())
    }
    fn print_heap<S: Pretty>(
        &mut self,
        heap: &ast::Heap<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        for (i, (l, ty)) in heap.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            self.print_location(l, f)?;
            write!(f, ": ")?;
            self.print_ty(ty, f)?;
        }
        Ok(())
    }

    fn print_ty<S: Pretty>(&mut self, ty: &ast::Ty<S>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match ty {
            ast::Ty::OwnRef(l) => {
                write!(f, "own(")?;
                self.print_location(l, f)?;
                write!(f, ")")?;
            }
            ast::Ty::Ref(bk, _r, l) => {
                let bk = match bk {
                    ast::BorrowKind::Shared => "",
                    ast::BorrowKind::Mut => "mut",
                };
                write!(f, "&{}(..., ", bk)?;
                self.print_location(l, f)?;
                write!(f, ")")?;
            }
            ast::Ty::Tuple(tup) => {
                write!(f, "(")?;
                for (i, (fld, ty)) in tup.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    self.print_field(fld, f)?;
                    write!(f, ": ")?;
                    self.print_ty(ty, f)?;
                }
                write!(f, ")")?;
            }
            ast::Ty::Uninit(size) => {
                write!(f, "Uninit({})", size)?;
            }
            ast::Ty::Refine(bty, refine) => {
                write!(f, "{{ ")?;
                self.print_base_ty(bty, f)?;
                write!(f, " | ")?;
                match refine {
                    ast::Refine::Infer => write!(f, "_")?,
                    ast::Refine::Pred(_) => write!(f, "...")?,
                }
                write!(f, " }}")?;
            }
        }
        Ok(())
    }

    fn print_type_layout(
        &mut self,
        layout: &ast::TypeLayout,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match layout {
            ast::TypeLayout::Tuple(tup) => {
                write!(f, "(")?;
                for (i, layout) in tup.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    self.print_type_layout(layout, f)?;
                }
                write!(f, ")")?;
            }
            ast::TypeLayout::Block(size) => {
                write!(f, "{}", size)?;
            }
        }
        Ok(())
    }

    fn print_base_ty(&mut self, bty: &ast::BaseTy, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match bty {
            ast::BaseTy::Unit => write!(f, "()"),
            ast::BaseTy::Bool => write!(f, "bool"),
            ast::BaseTy::Int => write!(f, "int"),
        }
    }

    fn print_place<S: Pretty>(
        &mut self,
        place: &ast::Place<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        self.print_local(&place.base, f)?;
        let mut s = String::new();
        let mut need_parens = false;
        for proj in &place.projs {
            match proj {
                ast::Proj::Field(n) => {
                    if need_parens {
                        s = format!("({}).{}", s, n);
                        need_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                ast::Proj::Deref => {
                    s = format!("*{}", s);
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }

    fn print_cont_id<S: Pretty>(
        &mut self,
        cont_id: &ContId<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        cont_id.0.print(f)
    }

    fn print_local<S: Pretty>(&mut self, x: &Local<S>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        x.0.print(f)
    }

    fn print_location<S: Pretty>(
        &mut self,
        l: &Location<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        l.0.print(f)
    }

    fn print_field<S: Pretty>(
        &mut self,
        fld: &Field<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        fld.0.print(f)
    }
}

pub trait Pretty {
    fn print(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}
impl<T: fmt::Display> Pretty for T {
    fn print(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}
