use crate::{
    ast::{
        BinOpKind as AstBinOpKind, Predicate as AstPredicate, PredicateKind as AstPredicateKind,
        UnOpKind as AstUnOpKind,
    },
    resolution::{
        solve::{ResolutionErrorKind, ResolutionResult, Solve},
        ResolutionCtx,
    },
};

use liquid_rust_ty::{BaseTy, BinOp, Predicate, UnOp};

impl<'source> Solve<'source> for AstPredicate<'source> {
    type Output = Predicate;

    fn solve(
        &self,
        rcx: &mut ResolutionCtx<'source>,
    ) -> ResolutionResult<'source, (Self::Output, BaseTy)> {
        match &self.kind {
            AstPredicateKind::Lit(literal) => {
                // literal predicates do not need to be solved.
                let predicate = Predicate::Lit(*literal);
                let base_ty = literal.base_ty();

                Ok((predicate, base_ty))
            }
            AstPredicateKind::Var(ident) => {
                // variable predicates can be solved by solving their identifier.
                let (variable, base_ty) = rcx.solve(ident)?;

                Ok((Predicate::Var(variable), base_ty))
            }
            AstPredicateKind::UnaryOp(un_op, op) => {
                // solve the operand.
                let (op, op_ty) = rcx.solve(op.as_ref())?;
                // check if the type of the operand is valid for the operator.
                let (un_op, ty) = match (un_op.kind, op_ty) {
                    // the logical negation of a boolean is a valid operation that returns a
                    // boolean.
                    (AstUnOpKind::Not, BaseTy::Bool) => (UnOp::Not, BaseTy::Bool),
                    // the bitwise negation of an integer is a valid operation that returns the
                    // same integer type.
                    (AstUnOpKind::Neg, BaseTy::Int(sign, size)) => {
                        (UnOp::Neg(sign, size), BaseTy::Int(sign, size))
                    }
                    // any other combination of operator and operand type is invalid.
                    (kind, ty) => {
                        return ResolutionErrorKind::InvalidUnaryOp(kind, ty)
                            .into_err(self.span.clone())
                    }
                };

                Ok((Predicate::UnaryOp(un_op, Box::new(op)), ty))
            }
            AstPredicateKind::BinaryOp(bin_op, op1, op2) => {
                // solve both operands.
                let (op1, op_ty1) = rcx.solve(op1.as_ref())?;
                let (op2, op_ty2) = rcx.solve(op2.as_ref())?;
                // for now, both operands must have the same type for the operations to be valid.
                // This is not the case for bitwise shifts and offsets.
                if op_ty1 != op_ty2 {
                    return ResolutionErrorKind::InvalidBinaryOp(bin_op.kind, op_ty1, op_ty2)
                        .into_err(self.span.clone());
                }

                // check if the types of the operands is valid for the operator.
                let (bin_op, ty) = match (bin_op.kind, op_ty1) {
                    // any arithmetic operation of two integers is a valid operation that returns
                    // an integer of the same type.
                    (AstBinOpKind::Add, BaseTy::Int(sign, size)) => {
                        (BinOp::Add(sign, size), op_ty2)
                    }
                    (AstBinOpKind::Sub, BaseTy::Int(sign, size)) => {
                        (BinOp::Sub(sign, size), op_ty2)
                    }
                    (AstBinOpKind::Mul, BaseTy::Int(sign, size)) => {
                        (BinOp::Mul(sign, size), op_ty2)
                    }
                    (AstBinOpKind::Div, BaseTy::Int(sign, size)) => {
                        (BinOp::Div(sign, size), op_ty2)
                    }
                    (AstBinOpKind::Rem, BaseTy::Int(sign, size)) => {
                        (BinOp::Rem(sign, size), op_ty2)
                    }
                    // any logical operation between booleans is a valid operation that returns a
                    // boolean.
                    (AstBinOpKind::And, BaseTy::Bool) => (BinOp::And, BaseTy::Bool),
                    (AstBinOpKind::Or, BaseTy::Bool) => (BinOp::Or, BaseTy::Bool),
                    // any equality operation between operands of the same type is a valid
                    // operation that returns a boolean.
                    (AstBinOpKind::Eq, ty) => (BinOp::Eq(ty), BaseTy::Bool),
                    (AstBinOpKind::Neq, ty) => (BinOp::Neq(ty), BaseTy::Bool),
                    // any comparison operation between integers is a valid operation that returns
                    // a boolean.
                    (AstBinOpKind::Lt, BaseTy::Int(sign, size)) => {
                        (BinOp::Lt(sign, size), BaseTy::Bool)
                    }
                    (AstBinOpKind::Gt, BaseTy::Int(sign, size)) => {
                        (BinOp::Gt(sign, size), BaseTy::Bool)
                    }
                    (AstBinOpKind::Lte, BaseTy::Int(sign, size)) => {
                        (BinOp::Lte(sign, size), BaseTy::Bool)
                    }
                    (AstBinOpKind::Gte, BaseTy::Int(sign, size)) => {
                        (BinOp::Gte(sign, size), BaseTy::Bool)
                    }
                    // any other combination of operator and operand type is invalid.
                    (kind, ty1) => {
                        return ResolutionErrorKind::InvalidBinaryOp(kind, ty1, op_ty2)
                            .into_err(self.span.clone())
                    }
                };

                Ok((
                    Predicate::BinaryOp(bin_op, Box::new(op1), Box::new(op2)),
                    ty,
                ))
            }
        }
    }
}
