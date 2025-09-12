use crate::{Types, constraint::Constraint};

#[cfg(feature = "rust-fixpoint")]
mod rust_fixpoint {
    use core::panic;
    use std::collections::HashMap;

    use z3::{
        Config, Context, SatResult, Solver, SortKind,
        ast::{self, Ast},
    };

    use crate::{
        FixpointFmt, Identifier, Types,
        constraint::{BinOp, BinRel, Bind, Constant, Constraint, Expr, Pred, Sort},
    };
    struct Env<'ctx, T: Types> {
        bindings: HashMap<T::Var, Vec<ast::Dynamic<'ctx>>>,
    }

    impl<'ctx, T: Types> Env<'ctx, T> {
        fn new() -> Self {
            Self { bindings: HashMap::new() }
        }

        fn insert(&mut self, name: T::Var, value: ast::Dynamic<'ctx>) {
            self.bindings.entry(name).or_default().push(value);
        }

        fn pop(&mut self, name: &T::Var) {
            if let Some(stack) = self.bindings.get_mut(name) {
                stack.pop();
                if stack.is_empty() {
                    self.bindings.remove(name);
                }
            }
        }

        fn lookup(&self, name: &T::Var) -> Option<ast::Dynamic<'ctx>> {
            self.bindings
                .get(name)
                .and_then(|stack| stack.last().cloned())
        }
    }

    fn const_to_z3<'ctx, T: Types>(ctx: &'ctx Context, cnst: &Constant<T>) -> ast::Dynamic<'ctx> {
        match cnst {
            Constant::Numeral(num) => ast::Int::from_i64(ctx, (*num).try_into().unwrap()).into(),
            Constant::Boolean(b) => ast::Bool::from_bool(ctx, *b).into(),
            Constant::String(strconst) => {
                ast::String::from_str(ctx, &strconst.display().to_string())
                    .unwrap()
                    .into()
            }
            _ => panic!("handling for this kind of const isn't implemented yet"),
        }
    }

    fn atom_to_z3<'ctx, T: Types>(
        ctx: &'ctx Context,
        bin_rel: &BinRel,
        operands: &Box<[Expr<T>; 2]>,
        env: &mut Env<'ctx, T>,
    ) -> ast::Dynamic<'ctx> {
        let loperand = expr_to_z3(ctx, &operands[0], env);
        let roperand = expr_to_z3(ctx, &operands[1], env);
        if loperand.sort_kind() != roperand.sort_kind() {
            panic!("Operands must have the same sort");
        }
        if !matches!(bin_rel, BinRel::Eq | BinRel::Ne)
            && !matches!(loperand.sort_kind(), SortKind::Int | SortKind::Real)
        {
            panic!("Comparison operators require numeric operands");
        }
        match (bin_rel, loperand.sort_kind(), roperand.sort_kind()) {
            (BinRel::Ne, _, _) => loperand._eq(&roperand).not().into(),
            (BinRel::Eq, _, _) => loperand._eq(&roperand).into(),
            (BinRel::Gt, SortKind::Int, SortKind::Int) => {
                let iloperand = loperand.as_int().expect("already checked");
                let iroperand = roperand.as_int().expect("already checked");
                iloperand.gt(&iroperand).into()
            }
            (BinRel::Gt, SortKind::Real, SortKind::Real) => {
                let rloperand = loperand.as_real().expect("already checked");
                let rroperand = roperand.as_real().expect("already checked");
                rloperand.gt(&rroperand).into()
            }
            (BinRel::Ge, SortKind::Int, SortKind::Int) => {
                let iloperand = loperand.as_int().expect("already checked");
                let iroperand = roperand.as_int().expect("already checked");
                iloperand.ge(&iroperand).into()
            }
            (BinRel::Ge, SortKind::Real, SortKind::Real) => {
                let rloperand = loperand.as_real().expect("already checked");
                let rroperand = roperand.as_real().expect("already checked");
                rloperand.ge(&rroperand).into()
            }
            (BinRel::Lt, SortKind::Int, SortKind::Int) => {
                let iloperand = loperand.as_int().expect("already checked");
                let iroperand = roperand.as_int().expect("already checked");
                iloperand.lt(&iroperand).into()
            }
            (BinRel::Lt, SortKind::Real, SortKind::Real) => {
                let rloperand = loperand.as_real().expect("already checked");
                let rroperand = roperand.as_real().expect("already checked");
                rloperand.lt(&rroperand).into()
            }
            (BinRel::Le, SortKind::Int, SortKind::Int) => {
                let iloperand = loperand.as_int().expect("already checked");
                let iroperand = roperand.as_int().expect("already checked");
                iloperand.le(&iroperand).into()
            }
            (BinRel::Le, SortKind::Real, SortKind::Real) => {
                let rloperand = loperand.as_real().expect("already checked");
                let rroperand = roperand.as_real().expect("already checked");
                rloperand.le(&rroperand).into()
            }
            _ => panic!("Unsupported relation or operand types"),
        }
    }

    fn binop_to_z3<'ctx, T: Types>(
        ctx: &'ctx Context,
        bin_op: &BinOp,
        operands: &Box<[Expr<T>; 2]>,
        env: &mut Env<'ctx, T>,
    ) -> ast::Dynamic<'ctx> {
        let lhs = expr_to_z3(ctx, &operands[0], env);
        let rhs = expr_to_z3(ctx, &operands[1], env);

        if lhs.sort_kind() != rhs.sort_kind() {
            panic!("binary operands must have the same sort");
        }

        match lhs.sort_kind() {
            // ------------------------------------------------------------------
            // ✦  Integers  ✦
            // ------------------------------------------------------------------
            SortKind::Int => {
                let l: ast::Int<'ctx> = lhs.as_int().unwrap();
                let r: ast::Int<'ctx> = rhs.as_int().unwrap();

                let res = match bin_op {
                    BinOp::Add => ast::Int::add(ctx, &[&l, &r]),
                    BinOp::Sub => ast::Int::sub(ctx, &[&l, &r]),
                    BinOp::Mul => ast::Int::mul(ctx, &[&l, &r]),
                    BinOp::Div => l.div(&r),
                    BinOp::Mod => l.modulo(&r),
                };
                res.into()
            }
            SortKind::Real => {
                let l: ast::Real<'ctx> = lhs.as_real().unwrap();
                let r: ast::Real<'ctx> = rhs.as_real().unwrap();

                let res = match bin_op {
                    BinOp::Add => ast::Real::add(ctx, &[&l, &r]),
                    BinOp::Sub => ast::Real::sub(ctx, &[&l, &r]),
                    BinOp::Mul => ast::Real::mul(ctx, &[&l, &r]),
                    BinOp::Div => l.div(&r),
                    BinOp::Mod => panic!("modulo is not defined on Real numbers"),
                };
                res.into()
            }

            _ => panic!("arithmetic operators only support Int and Real"),
        }
    }

    fn expr_to_z3<'ctx, T: Types>(
        ctx: &'ctx Context,
        expr: &Expr<T>,
        env: &mut Env<'ctx, T>,
    ) -> ast::Dynamic<'ctx> {
        match expr {
            Expr::Var(var) => env.lookup(var).expect("error if not present"),
            Expr::Constant(cnst) => const_to_z3(ctx, cnst),
            Expr::Atom(bin_rel, operands) => atom_to_z3(ctx, bin_rel, operands, env),
            Expr::BinaryOp(bin_op, operands) => binop_to_z3(ctx, bin_op, operands, env),
            Expr::And(conjuncts) => {
                let booleans = conjuncts
                    .iter()
                    .map(|conjunct| expr_to_z3(ctx, conjunct, env).as_bool())
                    .collect::<Option<Vec<_>>>()
                    .unwrap();
                let boolean_refs: Vec<&ast::Bool> = booleans.iter().collect();
                let bool_ref_slice: &[&ast::Bool] = boolean_refs.as_slice();
                ast::Bool::and(ctx, bool_ref_slice).into()
            }
            Expr::Or(options) => {
                let booleans = options
                    .iter()
                    .map(|option| expr_to_z3(ctx, option, env).as_bool())
                    .collect::<Option<Vec<_>>>()
                    .unwrap();
                let boolean_refs: Vec<&ast::Bool> = booleans.iter().collect();
                let bool_ref_slice: &[&ast::Bool] = boolean_refs.as_slice();
                ast::Bool::or(ctx, bool_ref_slice).into()
            }
            Expr::Not(inner) => {
                expr_to_z3(ctx, &*inner, env)
                    .as_bool()
                    .unwrap()
                    .not()
                    .into()
            }
            Expr::Neg(number) => {
                let zero = ast::Int::from_i64(ctx, 0);
                let z3_num = expr_to_z3(ctx, &number, env);
                match z3_num.sort_kind() {
                    SortKind::Int => ast::Int::sub(ctx, &[&zero, &z3_num.as_int().unwrap()]).into(),
                    SortKind::Real => {
                        ast::Real::sub(ctx, &[&zero.to_real(), &z3_num.as_real().unwrap()]).into()
                    }
                    _ => panic!("Negation requires numeric operand"),
                }
            }
            Expr::Iff(operands) => {
                let lhs = expr_to_z3(ctx, &operands[0], env);
                let rhs = expr_to_z3(ctx, &operands[1], env);
                lhs.as_bool().unwrap().iff(&rhs.as_bool().unwrap()).into()
            }
            Expr::Imp(operands) => {
                let lhs = expr_to_z3(ctx, &operands[0], env);
                let rhs = expr_to_z3(ctx, &operands[1], env);
                lhs.as_bool()
                    .unwrap()
                    .implies(&rhs.as_bool().unwrap())
                    .into()
            }
            Expr::Let(variable, exprs) => {
                let binding = expr_to_z3(ctx, &exprs[0], env);
                env.insert(variable.clone(), binding);
                let res = expr_to_z3(ctx, &exprs[1], env);
                env.pop(&variable);
                res
            }
            _ => {
                panic!("handling for this kind of expression is not implemented yet")
            }
        }
    }

    fn pred_to_z3<'ctx, T: Types>(
        ctx: &'ctx Context,
        pred: &Pred<T>,
        env: &mut Env<'ctx, T>,
    ) -> ast::Bool<'ctx> {
        match pred {
            Pred::Expr(expr) => expr_to_z3(ctx, expr, env).as_bool().expect(" asldfj "),
            Pred::And(conjuncts) => {
                let bools: Vec<_> = conjuncts
                    .iter()
                    .map(|conjunct| pred_to_z3(ctx, conjunct, env))
                    .collect::<Vec<_>>();
                let bool_refs: Vec<&ast::Bool> = bools.iter().collect();
                ast::Bool::and(ctx, bool_refs.as_slice()).into()
            }
            Pred::KVar(_kvar, _vars) => panic!("Kvars not supported yet"),
        }
    }

    fn new_const<'ctx, T: Types>(ctx: &'ctx Context, bind: &Bind<T>) -> ast::Dynamic<'ctx> {
        match &bind.sort {
            Sort::Int => ast::Int::new_const(ctx, bind.name.display().to_string().as_str()).into(),
            Sort::Real => {
                ast::Real::new_const(ctx, bind.name.display().to_string().as_str()).into()
            }
            Sort::Bool => {
                ast::Bool::new_const(ctx, bind.name.display().to_string().as_str()).into()
            }
            Sort::Str => {
                ast::String::new_const(ctx, bind.name.display().to_string().as_str()).into()
            }
            _ => panic!("unhandled kind encountered"),
        }
    }

    fn is_constraint_satisfiable_inner<'ctx, T: Types>(
        ctx: &'ctx Context,
        cstr: &Constraint<T>,
        solver: &Solver,
        env: &mut Env<'ctx, T>,
    ) -> bool {
        solver.push();
        let res = match cstr {
            Constraint::Pred(pred, _tag) => {
                solver.assert(&pred_to_z3(ctx, pred, env).not());
                matches!(solver.check(), SatResult::Unsat)
            }
            Constraint::Conj(conjuncts) => {
                conjuncts
                    .iter()
                    .all(|conjunct| is_constraint_satisfiable_inner(ctx, conjunct, solver, env))
            }

            Constraint::ForAll(bind, inner) => {
                env.insert(bind.name.clone(), new_const(ctx, bind));
                solver.assert(&pred_to_z3(ctx, &bind.pred, env));
                let inner_soln = is_constraint_satisfiable_inner(ctx, &**inner, solver, env);
                env.pop(&bind.name);
                inner_soln
            }
        };
        solver.pop(1);
        res
    }

    pub fn is_constraint_satisfiable<T: Types>(cstr: &Constraint<T>) -> bool {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let mut vars = Env::new();
        is_constraint_satisfiable_inner(&ctx, &cstr, &solver, &mut vars)
    }
}

#[cfg(feature = "rust-fixpoint")]
pub fn is_constraint_satisfiable<T: Types>(cstr: &Constraint<T>) -> bool {
    rust_fixpoint::is_constraint_satisfiable(cstr)
}

#[cfg(not(feature = "rust-fixpoint"))]
pub fn is_constraint_satisfiable<T: Types>(_cstr: &Constraint<T>) -> bool {
    true
}
