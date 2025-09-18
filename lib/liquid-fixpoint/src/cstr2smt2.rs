use core::panic;
use std::{collections::HashMap, vec};

use z3::{
    Config, Context, FuncDecl, SatResult, Solver, SortKind,
    ast::{self, Ast},
};

use crate::{
    ConstDecl, Error, FixpointFmt, FixpointResult, Identifier, Stats, Types,
    constraint::{BinOp, BinRel, Constant, Constraint, Expr, Pred, Sort},
};

#[derive(Debug)]
enum Binding<'ctx> {
    Variable(ast::Dynamic<'ctx>),
    Function(FuncDecl<'ctx>),
}

impl<'ctx> From<ast::Dynamic<'ctx>> for Binding<'ctx> {
    fn from(value: ast::Dynamic<'ctx>) -> Self {
        Binding::Variable(value)
    }
}

impl<'ctx> From<FuncDecl<'ctx>> for Binding<'ctx> {
    fn from(value: FuncDecl<'ctx>) -> Self {
        Binding::Function(value)
    }
}

pub struct Env<'ctx, T: Types> {
    bindings: HashMap<T::Var, Vec<Binding<'ctx>>>,
}

impl<'ctx, T: Types> Env<'ctx, T> {
    fn new() -> Self {
        Self { bindings: HashMap::new() }
    }

    fn insert<B: Into<Binding<'ctx>>>(&mut self, name: T::Var, value: B) {
        self.bindings
            .entry(name)
            .or_default()
            .push(Into::<Binding<'ctx>>::into(value));
    }

    fn pop(&mut self, name: &T::Var) {
        if let Some(stack) = self.bindings.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.bindings.remove(name);
            }
        }
    }

    fn var_lookup(&self, name: &T::Var) -> Option<&ast::Dynamic<'ctx>> {
        match &self.lookup(name) {
            Some(Binding::Variable(var)) => Some(var),
            _ => None,
        }
    }

    fn fun_lookup(&self, name: &T::Var) -> Option<&FuncDecl<'ctx>> {
        match &self.lookup(name) {
            Some(Binding::Function(fun)) => Some(fun),
            _ => None,
        }
    }

    fn lookup(&self, name: &T::Var) -> Option<&Binding<'ctx>> {
        self.bindings.get(name).and_then(|stack| stack.last())
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
    let lhs = expr_to_z3(ctx, &operands[0], env);
    let rhs = expr_to_z3(ctx, &operands[1], env);
    if lhs.sort_kind() != rhs.sort_kind() {
        panic!("Operands must have the same sort");
    }
    if !matches!(bin_rel, BinRel::Eq | BinRel::Ne)
        && !matches!(lhs.sort_kind(), SortKind::Int | SortKind::Real)
    {
        panic!("Comparison operators require numeric operands");
    }
    match (bin_rel, lhs.sort_kind(), rhs.sort_kind()) {
        (BinRel::Ne, _, _) => lhs._eq(&rhs).not().into(),
        (BinRel::Eq, _, _) => lhs._eq(&rhs).into(),
        (BinRel::Gt, SortKind::Int, SortKind::Int) => {
            let ilhs = lhs.as_int().expect("already checked");
            let irhs = rhs.as_int().expect("already checked");
            ilhs.gt(&irhs).into()
        }
        (BinRel::Gt, SortKind::Real, SortKind::Real) => {
            let rlhs = lhs.as_real().expect("already checked");
            let rrhs = rhs.as_real().expect("already checked");
            rlhs.gt(&rrhs).into()
        }
        (BinRel::Ge, SortKind::Int, SortKind::Int) => {
            let ilhs = lhs.as_int().expect("already checked");
            let irhs = rhs.as_int().expect("already checked");
            ilhs.ge(&irhs).into()
        }
        (BinRel::Ge, SortKind::Real, SortKind::Real) => {
            let rlhs = lhs.as_real().expect("already checked");
            let rrhs = rhs.as_real().expect("already checked");
            rlhs.ge(&rrhs).into()
        }
        (BinRel::Lt, SortKind::Int, SortKind::Int) => {
            let ilhs = lhs.as_int().expect("already checked");
            let irhs = rhs.as_int().expect("already checked");
            ilhs.lt(&irhs).into()
        }
        (BinRel::Lt, SortKind::Real, SortKind::Real) => {
            let rlhs = lhs.as_real().expect("already checked");
            let rrhs = rhs.as_real().expect("already checked");
            rlhs.lt(&rrhs).into()
        }
        (BinRel::Le, SortKind::Int, SortKind::Int) => {
            let ilhs = lhs.as_int().expect("already checked");
            let irhs = rhs.as_int().expect("already checked");
            ilhs.le(&irhs).into()
        }
        (BinRel::Le, SortKind::Real, SortKind::Real) => {
            let rlhs = lhs.as_real().expect("already checked");
            let rrhs = rhs.as_real().expect("already checked");
            rlhs.le(&rrhs).into()
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
        Expr::Var(var) => {
            env.var_lookup(var)
                .map(|var| var.clone())
                .expect("error if not present")
        }
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
        Expr::App(fun, args) => {
            match &**fun {
                Expr::Var(var) => {
                    let arg_asts: Vec<Box<dyn Ast<'ctx>>> = args
                        .iter()
                        .map(|arg| dynamic_as_ast(expr_to_z3(ctx, arg, env)))
                        .collect();
                    let arg_refs: Vec<&_> = arg_asts.iter().map(|a| a.as_ref()).collect();
                    let fun_decl = env.fun_lookup(var).expect("error if function not present");
                    fun_decl.apply(&arg_refs)
                }
                _ => panic!("encountered function application but no function"),
            }
        }
        _ => {
            panic!("handling for this kind of expression is not implemented yet")
        }
    }
}

fn dynamic_as_ast<'ctx>(val: ast::Dynamic<'ctx>) -> Box<dyn Ast<'ctx> + 'ctx> {
    if let Some(int_val) = val.as_int() {
        Box::new(int_val) as Box<dyn Ast<'ctx>>
    } else if let Some(real_val) = val.as_real() {
        Box::new(real_val) as Box<dyn Ast<'ctx>>
    } else if let Some(bool_val) = val.as_bool() {
        Box::new(bool_val) as Box<dyn Ast<'ctx>>
    } else if let Some(str_val) = val.as_string() {
        Box::new(str_val) as Box<dyn Ast<'ctx>>
    } else {
        panic!("unhandled sort encountered")
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

fn new_binding<'ctx, T: Types>(ctx: &'ctx Context, name: &T::Var, sort: &Sort<T>) -> Binding<'ctx> {
    match &sort {
        Sort::Int => {
            Binding::Variable(ast::Int::new_const(ctx, name.display().to_string().as_str()).into())
        }
        Sort::Real => {
            Binding::Variable(ast::Real::new_const(ctx, name.display().to_string().as_str()).into())
        }
        Sort::Bool => {
            Binding::Variable(ast::Bool::new_const(ctx, name.display().to_string().as_str()).into())
        }
        Sort::Str => {
            Binding::Variable(
                ast::String::new_const(ctx, name.display().to_string().as_str()).into(),
            )
        }
        Sort::Func(sorts) => {
            let fun_decl = FuncDecl::new(
                ctx,
                name.display().to_string().as_str(),
                &[&z3_sort(ctx, &(*sorts)[0])],
                &z3_sort(ctx, &(*sorts)[1]),
            );
            Binding::Function(fun_decl)
        }
        &s => panic!("unhandled kind encountered: {:#?}", s),
    }
}

fn z3_sort<'ctx, T: Types>(ctx: &'ctx Context, s: &Sort<T>) -> z3::Sort<'ctx> {
    match &s {
        Sort::Int => z3::Sort::int(ctx),
        Sort::Real => z3::Sort::real(ctx),
        Sort::Bool => z3::Sort::bool(ctx),
        Sort::Str => z3::Sort::string(ctx),
        _ => panic!("unhandled sort encountered"),
    }
}

fn is_constraint_satisfiable_inner<'ctx, T: Types>(
    ctx: &'ctx Context,
    cstr: &Constraint<T>,
    solver: &Solver,
    env: &mut Env<'ctx, T>,
) -> FixpointResult<T::Tag> {
    solver.push();
    let res = match cstr {
        Constraint::Pred(pred, tag) => {
            solver.assert(&pred_to_z3(ctx, pred, env).not());
            if solver.check() == SatResult::Unsat {
                FixpointResult::Safe(Stats { num_cstr: 1, num_iter: 0, num_chck: 0, num_vald: 0 })
            } else {
                FixpointResult::Unsafe(
                    Stats { num_cstr: 1, num_iter: 0, num_chck: 0, num_vald: 0 },
                    match tag {
                        Some(tag) => vec![Error { id: 0, tag: tag.clone() }],
                        None => vec![],
                    },
                )
            }
        }
        Constraint::Conj(conjuncts) => {
            conjuncts.iter().fold(
                FixpointResult::Safe(Stats { num_cstr: 0, num_iter: 0, num_chck: 0, num_vald: 0 }),
                |acc, cstr| is_constraint_satisfiable_inner(ctx, cstr, solver, env).merge(acc),
            )
        }

        Constraint::ForAll(bind, inner) => {
            env.insert(bind.name.clone(), new_binding(ctx, &bind.name, &bind.sort));
            solver.assert(&pred_to_z3(ctx, &bind.pred, env));
            let inner_soln = is_constraint_satisfiable_inner(ctx, &**inner, solver, env);
            env.pop(&bind.name);
            inner_soln
        }
    };
    solver.pop(1);
    res
}

pub fn is_constraint_satisfiable<T: Types>(
    cstr: &Constraint<T>,
    consts: &Vec<ConstDecl<T>>,
) -> FixpointResult<T::Tag> {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let mut vars = Env::new();
    consts.iter().for_each(|const_decl| {
        vars.insert(const_decl.name.clone(), new_binding(&ctx, &const_decl.name, &const_decl.sort))
    });
    is_constraint_satisfiable_inner(&ctx, &cstr, &solver, &mut vars)
}
