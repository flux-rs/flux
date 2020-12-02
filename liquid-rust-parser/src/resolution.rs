use crate::{
    ast::{
        BinOp as AstBinOp, Predicate as AstPredicate, Ty as AstTy, UnOp as AstUnOp,
        Variable as AstVariable,
    },
    ParseError, ParseErrorKind, ParseResult,
};

use liquid_rust_ty::{Argument, BaseTy, BinOp, FuncTy, Predicate, Ty, UnOp, Variable};

pub fn solve_ty<'source, V: Copy>(ast_ty: &AstTy<'source>) -> ParseResult<Ty<V>> {
    ResolutionCtx::new().solve_ty(ast_ty)
}

struct ResolutionCtx<'source, V> {
    scopes: Vec<Scope<'source, V>>,
}

impl<'source, V: Copy> ResolutionCtx<'source, V> {
    fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    fn solve_ty(&mut self, ast_ty: &AstTy<'source>) -> ParseResult<Ty<V>> {
        match ast_ty {
            AstTy::Base(base_ty) => Ok(base_ty.refined()),
            AstTy::Refined(bounded_variable, base_ty, predicate) => {
                self.push_variable(bounded_variable, Variable::Bounded, *base_ty);

                let (predicate, pred_ty) = self.solve_predicate(predicate)?;

                if pred_ty != BaseTy::Bool {
                    panic!("expected boolean, found {}", pred_ty);
                }

                self.pop_variable();

                Ok(Ty::Refined(*base_ty, predicate))
            }
            AstTy::Func(arguments, return_ty) => {
                self.push_scope();

                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(pos, (ast_argument, ast_ty))| {
                        let ty = self.solve_ty(ast_ty)?;

                        self.push_variable(
                            ast_argument,
                            Variable::Arg(Argument::new(pos)),
                            ty.get_base().expect("HOFs aren't here yet."),
                        );

                        Ok(ty)
                    })
                    .collect::<ParseResult<Vec<_>>>()?;

                let return_ty = self.solve_ty(return_ty.as_ref())?;

                for _ in 0..arguments.len() {
                    self.pop_variable();
                }

                self.pop_scope();

                Ok(Ty::Func(FuncTy::new(arguments, return_ty)))
            }
        }
    }

    fn solve_predicate(
        &self,
        ast_predicate: &AstPredicate<'source>,
    ) -> ParseResult<(Predicate<V>, BaseTy)> {
        let predicate = match ast_predicate {
            AstPredicate::Var(variable) => {
                let (variable, base_ty) = self.solve_variable(variable)?;
                (Predicate::Var(variable), base_ty)
            }
            AstPredicate::Lit(literal) => (Predicate::Lit(*literal), literal.base_ty()),
            AstPredicate::UnApp(AstUnOp::Neg, op) => {
                let (op, base_ty) = self.solve_predicate(op.as_ref())?;

                let un_op = match base_ty {
                    BaseTy::Int(sign, size) => UnOp::Neg(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (Predicate::UnApp(un_op, Box::new(op)), base_ty)
            }
            AstPredicate::UnApp(AstUnOp::Not, op) => {
                let (op, base_ty) = self.solve_predicate(op.as_ref())?;

                let un_op = match base_ty {
                    BaseTy::Bool => UnOp::Not,
                    BaseTy::Int(sign, size) => UnOp::IntNot(sign, size),
                    base_ty => panic!("expected integer or boolean, found {}", base_ty),
                };

                (Predicate::UnApp(un_op, Box::new(op)), base_ty)
            }
            AstPredicate::BinApp(AstBinOp::Add, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Add(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Sub, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Sub(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Mul, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Mul(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Div, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Div(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Rem, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Rem(sign, size),
                    base_ty => panic!("expected integer, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::And, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Bool => BinOp::And,
                    base_ty => panic!("expected boolean, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Or, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Bool => BinOp::Or,
                    base_ty => panic!("expected boolean, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    base_ty1,
                )
            }
            AstPredicate::BinApp(AstBinOp::Eq, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = BinOp::Eq(base_ty1);

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
            AstPredicate::BinApp(AstBinOp::Neq, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = BinOp::Neq(base_ty1);

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
            AstPredicate::BinApp(AstBinOp::Lt, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Lt(sign, size),
                    base_ty => panic!("expected int, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
            AstPredicate::BinApp(AstBinOp::Gt, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Gt(sign, size),
                    base_ty => panic!("expected int, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
            AstPredicate::BinApp(AstBinOp::Lte, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Lte(sign, size),
                    base_ty => panic!("expected int, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
            AstPredicate::BinApp(AstBinOp::Gte, op1, op2) => {
                let (op1, base_ty1) = self.solve_predicate(op1.as_ref())?;
                let (op2, base_ty2) = self.solve_predicate(op2.as_ref())?;

                assert_eq!(base_ty1, base_ty2);

                let bin_op = match base_ty1 {
                    BaseTy::Int(sign, size) => BinOp::Gte(sign, size),
                    base_ty => panic!("expected int, found {}", base_ty),
                };

                (
                    Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2)),
                    BaseTy::Bool,
                )
            }
        };

        Ok(predicate)
    }

    fn scope(&self) -> &Scope<'source, V> {
        self.scopes
            .last()
            .expect("There should be at least one scope.")
    }

    fn scope_mut(&mut self) -> &mut Scope<'source, V> {
        self.scopes
            .last_mut()
            .expect("There should be at least one scope.")
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop().expect("Stack for scopes is empty.");
    }

    fn solve_variable(
        &self,
        ast_variable: &AstVariable<'source>,
    ) -> ParseResult<(Variable<V>, BaseTy)> {
        self.scope().solve_variable(&ast_variable).ok_or_else(|| {
            ParseError::new(
                ParseErrorKind::UnboundedVariable(ast_variable.0.to_string()),
                vec![],
                ast_variable.1.clone(),
            )
        })
    }

    fn push_variable(
        &mut self,
        ast_variable: &AstVariable<'source>,
        variable: Variable<V>,
        base_ty: BaseTy,
    ) {
        self.scope_mut()
            .push_variable(ast_variable, variable, base_ty);
    }

    fn pop_variable(&mut self) {
        self.scope_mut().pop_variable()
    }
}

struct Scope<'source, V> {
    stack: Vec<(&'source str, Variable<V>, BaseTy)>,
}

impl<'source, V: Copy> Scope<'source, V> {
    fn new() -> Self {
        Self { stack: Vec::new() }
    }

    fn push_variable(
        &mut self,
        ast_variable: &AstVariable<'source>,
        variable: Variable<V>,
        base_ty: BaseTy,
    ) {
        self.stack.push((ast_variable.0, variable, base_ty));
    }

    fn pop_variable(&mut self) {
        self.stack
            .pop()
            .expect("Stack for the current scope is empty.");
    }

    fn solve_variable(&self, ast_variable: &AstVariable<'source>) -> Option<(Variable<V>, BaseTy)> {
        for (slice, variable, base_ty) in self.stack.iter().rev() {
            if slice == &ast_variable.0 {
                return Some((*variable, *base_ty));
            }
        }
        None
    }
}
