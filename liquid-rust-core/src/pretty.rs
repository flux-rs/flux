use crate::{ast, names::*};
use std::fmt;

macro_rules! indent {
    ($formatter:expr, $indent:expr) => {
        ::std::write!($formatter, "\n{:>1$}", "", $indent)
    };
}

macro_rules! join {
    ($f:expr, $sep:literal, $pat:pat in $it:expr => $block:expr) => {{
        for (i, $pat) in IntoIterator::into_iter($it).enumerate() {
            if i > 0 {
                write!($f, $sep)?;
            }
            $block;
        }
    }};
}

impl<I, S: fmt::Display> fmt::Display for ast::FnDef<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_fn_def(self, f, 0)
    }
}

impl<I, S: fmt::Display> fmt::Display for ast::FnBody<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_fn_body(self, f, 0)
    }
}

impl<I, S: fmt::Display> fmt::Display for ast::Statement<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_statement(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::Operand<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_operand(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::Ty<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_ty(self, f)
    }
}

impl<S: fmt::Display> fmt::Debug for ast::Ty<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::Pred<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_pred(self, f)
    }
}

impl<S: fmt::Display> fmt::Debug for ast::Pred<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::pred::Place<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_pred_place(self, f)
    }
}

impl<S: fmt::Display> fmt::Debug for ast::pred::Place<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::Rvalue<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrinter.print_rvalue(self, f)
    }
}

impl<S: fmt::Display> fmt::Display for ast::Heap<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        PrettyPrinter.print_heap(self, f)?;
        write!(f, "(")
    }
}

impl<S: fmt::Display> fmt::Debug for ast::Heap<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub struct PrettyPrinter;

impl PrettyPrinter {
    fn print_fn_def<I, S: fmt::Display>(
        &mut self,
        func: &ast::FnDef<I, S>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        write!(f, "fn ...")?;
        indent!(f, indent + 2)?;
        write!(f, "( ")?;
        self.print_heap(&func.ty.in_heap, f)?;
        indent!(f, indent + 2)?;
        write!(f, "; ")?;
        self.print_locals(func.params.iter().zip(&func.ty.inputs), f)?;
        indent!(f, indent + 2)?;
        write!(f, ") ret ")?;
        self.print_cont_id(&func.ret, f)?;
        write!(f, "(")?;
        self.print_heap(&func.ty.out_heap, f)?;
        write!(f, "; own(")?;
        self.print_location(&func.ty.output, f)?;
        write!(f, ")) = ")?;
        self.print_fn_body(&func.body, f, indent + 2)?;
        Ok(())
    }

    fn print_fn_body<I, S: fmt::Display>(
        &mut self,
        fn_body: &ast::FnBody<I, S>,
        f: &mut fmt::Formatter<'_>,
        indent: usize,
    ) -> fmt::Result {
        match fn_body {
            ast::FnBody::LetCont(defs, rest) => {
                indent!(f, indent)?;
                write!(f, "letcont ")?;
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        indent!(f, indent)?;
                        write!(f, "and ")?;
                    }
                    self.print_cont_def(def, f, indent + 2)?
                }
                indent!(f, indent)?;
                write!(f, "in")?;
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Ite { discr, then, else_ } => {
                indent!(f, indent)?;
                write!(f, "if ")?;
                self.print_place(discr, f)?;
                write!(f, " then")?;
                self.print_fn_body(then, f, indent + 2)?;
                indent!(f, indent)?;
                write!(f, "else")?;
                self.print_fn_body(else_, f, indent + 2)?;
            }
            ast::FnBody::Call {
                func: _func,
                args,
                ret,
            } => {
                indent!(f, indent)?;
                write!(f, "call ...(")?;
                join!(f, ", ", x in args => self.print_local(x, f)? );
                write!(f, ") ret ")?;
                self.print_cont_id(ret, f)?;
            }
            ast::FnBody::Jump { target, args } => {
                indent!(f, indent)?;
                write!(f, "jump ")?;
                self.print_cont_id(target, f)?;
                write!(f, "(")?;
                join!(f, ", ", x in args => self.print_local(x, f)?);
                write!(f, ")")?;
            }
            ast::FnBody::Seq(stmnt, rest) => {
                if !matches!(stmnt.kind, ast::StatementKind::Nop) {
                    indent!(f, indent)?;
                    self.print_statement(stmnt, f)?;
                    write!(f, ";")?;
                }
                self.print_fn_body(rest, f, indent)?;
            }
            ast::FnBody::Abort => {
                indent!(f, indent)?;
                write!(f, "abort")?;
            }
        }
        Ok(())
    }

    fn print_statement<I, S: fmt::Display>(
        &mut self,
        stmnt: &ast::Statement<I, S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match &stmnt.kind {
            ast::StatementKind::Let(x, layout) => {
                write!(f, "let ")?;
                self.print_local(x, f)?;
                write!(f, " = alloc(")?;
                self.print_type_layout(layout, f)?;
                write!(f, ")")?;
            }
            ast::StatementKind::Assign(place, rvalue) => {
                self.print_place(place, f)?;
                write!(f, " := ")?;
                self.print_rvalue(rvalue, f)?;
            }
            ast::StatementKind::Drop(place) => {
                write!(f, "drop(")?;
                self.print_place(place, f)?;
                write!(f, ")")?;
            }
            ast::StatementKind::Nop => {
                write!(f, "Nop")?;
            }
        };
        Ok(())
    }

    fn print_rvalue<S: fmt::Display>(
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
                        write!(f, "!")?;
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

    fn print_operand<S: fmt::Display>(
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

    fn print_cont_def<I, S: fmt::Display>(
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

    fn print_locals<
        'a,
        S: fmt::Display + 'a,
        I: IntoIterator<Item = (&'a Local<S>, &'a Location<S>)>,
    >(
        &mut self,
        params: I,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        join!(f, ", ", (x, l) in params => {
            self.print_local(x, f)?;
            write!(f, ": own(")?;
            self.print_location(l, f)?;
            write!(f, ")")?;
        });
        Ok(())
    }
    fn print_heap<S: fmt::Display>(
        &mut self,
        heap: &ast::Heap<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        join!(f, ", ", (l, ty) in heap => {
            self.print_location(l, f)?;
            write!(f, ": ")?;
            self.print_ty(ty, f)?;
        });
        Ok(())
    }

    fn print_ty<S: fmt::Display>(
        &mut self,
        ty: &ast::Ty<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
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
                join!(f, ", ", (fld, ty) in tup => {
                    self.print_field(fld, f)?;
                    write!(f, ": ")?;
                    self.print_ty(ty, f)?;
                });
                write!(f, ")")?;
            }
            ast::Ty::Uninit(size) => {
                write!(f, "uninit({})", size)?;
            }
            ast::Ty::Refine(bty, refine) => {
                write!(f, "{{ ")?;
                self.print_base_ty(bty, f)?;
                write!(f, " | ")?;
                match refine {
                    ast::Refine::Infer => write!(f, "_")?,
                    ast::Refine::Pred(pred) => self.print_pred(pred, f)?,
                }
                write!(f, " }}")?;
            }
        }
        Ok(())
    }

    fn print_pred<S: fmt::Display>(
        &mut self,
        pred: &ast::Pred<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match pred {
            ast::Pred::Constant(ast::pred::Constant::Bool(b)) => {
                write!(f, "{}", b)?;
            }
            ast::Pred::Constant(ast::pred::Constant::Int(n)) => {
                write!(f, "{}", n)?;
            }
            ast::Pred::Constant(ast::pred::Constant::Unit) => {
                write!(f, "()")?;
            }
            ast::Pred::Place(place) => {
                self.print_pred_place(place, f)?;
            }
            ast::Pred::BinaryOp(bin_op, op1, op2) => {
                write!(f, "(")?;
                self.print_pred(op1, f)?;
                write!(f, " ")?;
                self.print_pred_bin_op(bin_op, f)?;
                write!(f, " ")?;
                self.print_pred(op2, f)?;
                write!(f, ")")?;
            }
            ast::Pred::UnaryOp(_un_op, _op) => {
                write!(f, "...")?;
            }
        }
        Ok(())
    }

    fn print_pred_bin_op(
        &mut self,
        bin_op: &ast::pred::BinOp,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match bin_op {
            ast::pred::BinOp::Add => write!(f, "+"),
            ast::pred::BinOp::Sub => write!(f, "-"),
            ast::pred::BinOp::Lt => write!(f, "<"),
            ast::pred::BinOp::Le => write!(f, "<="),
            ast::pred::BinOp::Eq => write!(f, "="),
            ast::pred::BinOp::Ge => write!(f, ">="),
            ast::pred::BinOp::Gt => write!(f, ">"),
            ast::pred::BinOp::Iff => write!(f, "<=>"),
        }
    }

    fn print_pred_place<S: fmt::Display>(
        &mut self,
        place: &ast::pred::Place<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        self.print_var(&place.base, f)?;
        for proj in &place.projs {
            write!(f, ".{}", proj)?;
        }
        Ok(())
    }

    fn print_var<S: fmt::Display>(
        &mut self,
        var: &ast::pred::Var<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match var {
            crate::ty::Var::Nu => {
                write!(f, "V")?;
            }
            crate::ty::Var::Location(l) => {
                write!(f, "l{}", l.0)?;
            }
            crate::ty::Var::Field(fld) => {
                write!(f, "@{}", fld.0)?;
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
                join!(f, ", ", layout in tup => self.print_type_layout(layout, f)?);
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

    fn print_place<S: fmt::Display>(
        &mut self,
        place: &ast::Place<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let mut s = format!("_{}", place.base.0);
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

    fn print_cont_id<S: fmt::Display>(
        &mut self,
        cont_id: &ContId<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        write!(f, "bb{}", cont_id.0)
    }

    fn print_local<S: fmt::Display>(
        &mut self,
        x: &Local<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        write!(f, "_{}", x.0)
    }

    fn print_location<S: fmt::Display>(
        &mut self,
        l: &Location<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        write!(f, "l{}", l.0)
    }

    fn print_field<S: fmt::Display>(
        &mut self,
        fld: &Field<S>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        write!(f, "@{}", fld.0)
    }
}
