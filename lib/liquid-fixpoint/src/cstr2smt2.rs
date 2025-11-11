use core::panic;
use std::{collections::HashMap, iter, str::FromStr, vec};

use itertools::Itertools as _;
use z3::{
    FuncDecl, SatResult, Solver, SortKind,
    ast::{self, Ast},
};

use crate::{
    DataDecl, Error, FixpointFmt, FixpointStatus, Identifier, SortCtor, Stats, ThyFunc, Types,
    constraint::{BinOp, BinRel, Constant, Constraint, Expr, Pred, Sort},
};

#[derive(Debug)]
pub(crate) enum Binding {
    Variable(ast::Dynamic),
    Function(FuncDecl, ast::Dynamic),
}

impl From<ast::Dynamic> for Binding {
    fn from(value: ast::Dynamic) -> Self {
        Self::Variable(value)
    }
}

pub(crate) struct Env<T: Types> {
    bindings: HashMap<T::Var, Vec<Binding>>,
    data_types: HashMap<T::Sort, z3::Sort>,
}

impl<T: Types> Env<T> {
    pub(crate) fn new() -> Self {
        Self { bindings: HashMap::new(), data_types: HashMap::new() }
    }

    pub(crate) fn insert<B: Into<Binding>>(&mut self, name: T::Var, value: B) {
        self.bindings
            .entry(name)
            .or_default()
            .push(Into::<Binding>::into(value));
    }

    pub(crate) fn insert_data_decl(&mut self, name: T::Sort, datatype: z3::Sort) {
        self.data_types.insert(name, datatype);
    }

    fn pop(&mut self, name: &T::Var) {
        if let Some(stack) = self.bindings.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.bindings.remove(name);
            }
        }
    }

    fn var_lookup(&self, name: &T::Var) -> Option<&ast::Dynamic> {
        match &self.lookup(name) {
            Some(Binding::Variable(var)) => Some(var),
            Some(Binding::Function(_, c)) => Some(c),
            _ => None,
        }
    }

    fn fun_lookup(&self, name: &T::Var) -> Option<&FuncDecl> {
        match &self.lookup(name) {
            Some(Binding::Function(fun, _)) => Some(fun),
            _ => None,
        }
    }

    fn lookup(&self, name: &T::Var) -> Option<&Binding> {
        self.bindings.get(name).and_then(|stack| stack.last())
    }

    fn datatype_lookup(&self, name: &T::Sort) -> Option<&z3::Sort> {
        self.data_types.get(name)
    }
}

fn const_to_z3<T: Types>(cnst: &Constant<T>) -> ast::Dynamic {
    match cnst {
        Constant::Numeral(num) => ast::Int::from_str(&num.to_string()).unwrap().into(),
        Constant::Boolean(b) => ast::Bool::from_bool(*b).into(),
        Constant::String(strconst) => ast::String::from(strconst.display().to_string()).into(),
        Constant::BitVec(bv, size) => ast::BV::from_u64(*bv as u64, *size).into(),
        Constant::Real(num) => {
            ast::Real::from_rational_str(&num.to_string(), "1")
                .unwrap()
                .into()
        }
    }
}

fn atom_to_z3<T: Types>(
    bin_rel: &BinRel,
    operands: &[Expr<T>; 2],
    env: &mut Env<T>,
) -> ast::Dynamic {
    let lhs = expr_to_z3(&operands[0], env);
    let rhs = expr_to_z3(&operands[1], env);
    if lhs.sort_kind() != rhs.sort_kind() {
        panic!("Operands must have the same sort");
    }
    if !matches!(bin_rel, BinRel::Eq | BinRel::Ne)
        && !matches!(lhs.sort_kind(), SortKind::Int | SortKind::Real)
    {
        panic!("Comparison operators require numeric operands");
    }
    match (bin_rel, lhs.sort_kind(), rhs.sort_kind()) {
        (BinRel::Ne, _, _) => lhs.eq(&rhs).not().into(),
        (BinRel::Eq, _, _) => lhs.eq(&rhs).into(),
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

fn binop_to_z3<T: Types>(
    bin_op: &BinOp,
    operands: &[Expr<T>; 2],
    env: &mut Env<T>,
) -> ast::Dynamic {
    let lhs = expr_to_z3(&operands[0], env);
    let rhs = expr_to_z3(&operands[1], env);

    if lhs.sort_kind() != rhs.sort_kind() {
        panic!("binary operands must have the same sort");
    }

    match lhs.sort_kind() {
        // ------------------------------------------------------------------
        // ✦  Integers  ✦
        // ------------------------------------------------------------------
        SortKind::Int => {
            let l: ast::Int = lhs.as_int().unwrap();
            let r: ast::Int = rhs.as_int().unwrap();

            let res = match bin_op {
                BinOp::Add => ast::Int::add(&[&l, &r]),
                BinOp::Sub => ast::Int::sub(&[&l, &r]),
                BinOp::Mul => ast::Int::mul(&[&l, &r]),
                BinOp::Div => l.div(&r),
                BinOp::Mod => l.modulo(&r),
            };
            res.into()
        }
        SortKind::Real => {
            let l: ast::Real = lhs.as_real().unwrap();
            let r: ast::Real = rhs.as_real().unwrap();

            let res = match bin_op {
                BinOp::Add => ast::Real::add(&[&l, &r]),
                BinOp::Sub => ast::Real::sub(&[&l, &r]),
                BinOp::Mul => ast::Real::mul(&[&l, &r]),
                BinOp::Div => l.div(&r),
                BinOp::Mod => panic!("modulo is not defined on Real numbers"),
            };
            res.into()
        }

        _ => panic!("arithmetic operators only support Int and Real"),
    }
}

fn thy_func_application_to_z3<T: Types>(
    func: ThyFunc,
    args: &[Expr<T>],
    env: &mut Env<T>,
) -> ast::Dynamic {
    match func {
        ThyFunc::StrLen => {
            expr_to_z3(&args[0], env)
                .as_string()
                .unwrap()
                .length()
                .into()
        }
        ThyFunc::StrConcat => {
            let arg1 = expr_to_z3(&args[0], env).as_string().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_string().unwrap();
            ast::String::concat(&[arg1, arg2]).into()
        }
        ThyFunc::StrPrefixOf => {
            let arg1 = expr_to_z3(&args[0], env).as_string().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_string().unwrap();
            arg1.prefix(arg2).into()
        }
        ThyFunc::StrSuffixOf => {
            let arg1 = expr_to_z3(&args[0], env).as_string().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_string().unwrap();
            arg1.suffix(arg2).into()
        }
        ThyFunc::StrContains => {
            let arg1 = expr_to_z3(&args[0], env).as_string().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_string().unwrap();
            arg1.contains(arg2).into()
        }
        ThyFunc::SetMem => {
            let elem = expr_to_z3(&args[0], env);
            let set = expr_to_z3(&args[1], env).as_set().unwrap();
            set.member(&elem).into()
        }
        ThyFunc::SetEmpty => {
            panic!("cannot infer empty set element sort")
        }
        ThyFunc::SetSng => {
            let arg = expr_to_z3(&args[0], env);
            let arg_sort = arg.get_sort();
            let empty = ast::Set::empty(&arg_sort);
            empty.add(&arg).into()
        }
        ThyFunc::SetCup => {
            let arg1 = expr_to_z3(&args[0], env).as_set().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_set().unwrap();
            ast::Set::set_union(&[&arg1, &arg2]).into()
        }
        ThyFunc::SetCap => {
            let arg1 = expr_to_z3(&args[0], env).as_set().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_set().unwrap();
            ast::Set::intersect(&[&arg1, &arg2]).into()
        }
        ThyFunc::SetDif => {
            let arg1 = expr_to_z3(&args[0], env).as_set().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_set().unwrap();
            arg1.difference(arg2).into()
        }
        ThyFunc::SetSub => {
            let arg1 = expr_to_z3(&args[0], env).as_set().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_set().unwrap();
            arg1.set_subset(arg2).into()
        }
        ThyFunc::IntToBv32 => {
            let arg = expr_to_z3(&args[0], env).as_int().unwrap();
            ast::BV::from_int(&arg, 32).into()
        }
        ThyFunc::IntToBv64 => {
            let arg = expr_to_z3(&args[0], env).as_int().unwrap();
            ast::BV::from_int(&arg, 64).into()
        }
        ThyFunc::IntToBv8 => {
            let arg = expr_to_z3(&args[0], env).as_int().unwrap();
            ast::BV::from_int(&arg, 8).into()
        }
        ThyFunc::Bv32ToInt => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.to_int(false).into()
        }
        ThyFunc::Bv64ToInt => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.to_int(false).into()
        }
        ThyFunc::Bv8ToInt => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.to_int(false).into()
        }
        ThyFunc::BvAdd => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvadd(&arg2).into()
        }
        ThyFunc::BvSub => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsub(&arg2).into()
        }
        ThyFunc::BvMul => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvmul(&arg2).into()
        }
        ThyFunc::BvNeg => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.bvneg().into()
        }
        ThyFunc::BvSdiv => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsdiv(&arg2).into()
        }
        ThyFunc::BvSrem => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsrem(&arg2).into()
        }
        ThyFunc::BvUrem => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvurem(&arg2).into()
        }
        ThyFunc::BvUdiv => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvudiv(&arg2).into()
        }
        ThyFunc::BvAnd => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvand(&arg2).into()
        }
        ThyFunc::BvOr => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvor(&arg2).into()
        }
        ThyFunc::BvXor => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvxor(&arg2).into()
        }
        ThyFunc::BvNot => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.bvnot().into()
        }
        ThyFunc::BvSge => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsge(&arg2).into()
        }
        ThyFunc::BvSgt => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsgt(&arg2).into()
        }
        ThyFunc::BvSle => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvsle(&arg2).into()
        }
        ThyFunc::BvSlt => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvslt(&arg2).into()
        }
        ThyFunc::BvUge => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvuge(&arg2).into()
        }
        ThyFunc::BvUgt => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvugt(&arg2).into()
        }
        ThyFunc::BvUle => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvule(&arg2).into()
        }
        ThyFunc::BvUlt => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvult(&arg2).into()
        }
        ThyFunc::BvShl => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvshl(&arg2).into()
        }
        ThyFunc::BvLshr => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvlshr(&arg2).into()
        }
        ThyFunc::BvAshr => {
            let arg1 = expr_to_z3(&args[0], env).as_bv().unwrap();
            let arg2 = expr_to_z3(&args[1], env).as_bv().unwrap();
            arg1.bvashr(&arg2).into()
        }
        ThyFunc::BvZeroExtend(size) => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.zero_ext(size as u32).into()
        }
        ThyFunc::BvSignExtend(size) => {
            let arg = expr_to_z3(&args[0], env).as_bv().unwrap();
            arg.sign_ext(size as u32).into()
        }
        ThyFunc::MapSelect => {
            let map = expr_to_z3(&args[0], env).as_array().unwrap();
            let idx = expr_to_z3(&args[1], env);
            map.select(&idx)
        }
        ThyFunc::MapStore => {
            let map = expr_to_z3(&args[0], env).as_array().unwrap();
            let idx = expr_to_z3(&args[1], env);
            let val = expr_to_z3(&args[1], env);
            map.store(&idx, &val).into()
        }
        ThyFunc::MapDefault => todo!("map default needs the elaborated domain sort"),
    }
}

fn expr_to_z3<T: Types>(expr: &Expr<T>, env: &mut Env<T>) -> ast::Dynamic {
    match expr {
        Expr::Var(var) => env.var_lookup(var).cloned().expect("error if not present"),
        Expr::Constant(cnst) => const_to_z3(cnst),
        Expr::Atom(bin_rel, operands) => atom_to_z3(bin_rel, operands, env),
        Expr::BinaryOp(bin_op, operands) => binop_to_z3(bin_op, operands, env),
        Expr::And(conjuncts) => {
            let booleans = conjuncts
                .iter()
                .map(|conjunct| expr_to_z3(conjunct, env).as_bool())
                .collect::<Option<Vec<_>>>()
                .unwrap();
            let boolean_refs = booleans.iter().collect_vec();
            ast::Bool::and(&boolean_refs).into()
        }
        Expr::Or(options) => {
            let booleans = options
                .iter()
                .map(|option| expr_to_z3(option, env).as_bool())
                .collect::<Option<Vec<_>>>()
                .unwrap();
            let boolean_refs = booleans.iter().collect_vec();
            ast::Bool::or(&boolean_refs).into()
        }
        Expr::Not(inner) => expr_to_z3(inner, env).as_bool().unwrap().not().into(),
        Expr::Neg(number) => {
            let zero = ast::Int::from_i64(0);
            let z3_num = expr_to_z3(number, env);
            match z3_num.sort_kind() {
                SortKind::Int => ast::Int::sub(&[&zero, &z3_num.as_int().unwrap()]).into(),
                SortKind::Real => {
                    ast::Real::sub(&[&zero.to_real(), &z3_num.as_real().unwrap()]).into()
                }
                kind => {
                    panic!("Negation requires numeric operand - kind: `{kind:?}`, expr: `{expr:?}")
                }
            }
        }
        Expr::Iff(operands) => {
            let lhs = expr_to_z3(&operands[0], env);
            let rhs = expr_to_z3(&operands[1], env);
            lhs.as_bool().unwrap().iff(rhs.as_bool().unwrap()).into()
        }
        Expr::Imp(operands) => {
            let lhs = expr_to_z3(&operands[0], env);
            let rhs = expr_to_z3(&operands[1], env);
            lhs.as_bool()
                .unwrap()
                .implies(rhs.as_bool().unwrap())
                .into()
        }
        Expr::Let(variable, exprs) => {
            let binding = expr_to_z3(&exprs[0], env);
            env.insert(variable.clone(), binding);
            let res = expr_to_z3(&exprs[1], env);
            env.pop(variable);
            res
        }
        Expr::IfThenElse(exprs) => {
            let condition = expr_to_z3(&exprs[0], env).as_bool().unwrap();
            let if_true = expr_to_z3(&exprs[1], env);
            let if_false = expr_to_z3(&exprs[2], env);
            ast::Bool::ite(&condition, &if_true, &if_false)
        }
        Expr::App(fun, args) => {
            match &**fun {
                Expr::Var(var) => {
                    let arg_asts = args.iter().map(|arg| expr_to_z3(arg, env)).collect_vec();
                    let arg_refs = arg_asts.iter().map(|a| a as &dyn Ast).collect_vec();
                    let fun_decl = env
                        .fun_lookup(var)
                        .unwrap_or_else(|| panic!("error if function not present {var:#?}"));
                    fun_decl.apply(&arg_refs)
                }
                Expr::ThyFunc(func) => thy_func_application_to_z3(*func, args, env),
                _ => panic!("encountered function application but no function"),
            }
        }
        Expr::IsCtor(..) => todo!("testers not yet implemented"),
        Expr::ThyFunc(_) => {
            unreachable!("Should not encounter theory func outside of an application")
        }
        Expr::Exists(..) => todo!("exists not yet implemented"),
        Expr::BoundVar(_) => unreachable!("Bound vars should only be present in fixpoint's output"),
    }
}

fn pred_to_z3<T: Types>(pred: &Pred<T>, env: &mut Env<T>) -> ast::Bool {
    match pred {
        Pred::Expr(expr) => expr_to_z3(expr, env).as_bool().expect(" asldfj "),
        Pred::And(conjuncts) => {
            let bools = conjuncts
                .iter()
                .map(|conjunct| pred_to_z3(conjunct, env))
                .collect_vec();
            let bool_refs = bools.iter().collect_vec();
            ast::Bool::and(&bool_refs)
        }
        Pred::KVar(_kvar, _vars) => panic!("Kvars not supported yet"),
    }
}

pub(crate) fn new_datatype<T: Types>(
    name: &T::Sort,
    data_decl: &DataDecl<T>,
    env: &mut Env<T>,
) -> z3::Sort {
    let mut builder = z3::DatatypeBuilder::new(name.display().to_string());
    if data_decl.vars != 0 {
        panic!("Unexpected polymorphic datatype constructor encountered {}", name.display())
    }
    for data_ctor in &data_decl.ctors {
        let mut fields = Vec::new();
        let data_field_names = data_ctor
            .fields
            .iter()
            .map(|field| field.name.display().to_string())
            .collect_vec();
        for (name, field) in data_field_names.iter().zip(&data_ctor.fields) {
            fields.push((name.as_str(), z3::DatatypeAccessor::sort(z3_sort(&field.sort, env))));
        }
        builder = builder.variant(&data_ctor.name.display().to_string(), fields);
    }
    let z3::DatatypeSort { sort, variants } = builder.finish();
    for (data_ctor, variant) in iter::zip(&data_decl.ctors, variants) {
        let z3::DatatypeVariant { constructor, accessors, tester: _ } = variant;
        env.insert(
            data_ctor.name.clone(),
            Binding::Function(constructor, ast::Int::new_const(name.display().to_string()).into()),
        );
        for (field, accessor) in iter::zip(&data_ctor.fields, accessors) {
            env.insert(
                field.name.clone(),
                Binding::Function(
                    accessor,
                    ast::Int::new_const(field.name.display().to_string()).into(),
                ),
            );
        }
    }
    sort
}

pub(crate) fn new_binding<T: Types>(name: &T::Var, sort: &Sort<T>, env: &Env<T>) -> Binding {
    match &sort {
        Sort::Int => Binding::Variable(ast::Int::new_const(name.display().to_string()).into()),
        Sort::Real => Binding::Variable(ast::Real::new_const(name.display().to_string()).into()),
        Sort::Bool => Binding::Variable(ast::Bool::new_const(name.display().to_string()).into()),
        Sort::Str => Binding::Variable(ast::String::new_const(name.display().to_string()).into()),
        Sort::Func(sorts) => {
            let mut domain = vec![z3_sort(&sorts[0], env)];
            let mut current = sorts.as_ref();
            let mut range = &sorts[1];
            while let Sort::Func(sorts) = &current[1] {
                domain.push(z3_sort(&(*sorts)[0], env));
                range = &sorts[1];
                current = sorts.as_ref();
            }
            let domain_refs = domain.iter().collect_vec();
            let fun_decl =
                FuncDecl::new(name.display().to_string(), &domain_refs, &z3_sort(range, env));
            Binding::Function(fun_decl, ast::Int::new_const(name.display().to_string()).into())
        }
        Sort::BitVec(bv_size) => {
            match **bv_size {
                Sort::BvSize(size) => {
                    Binding::Variable(ast::BV::new_const(name.display().to_string(), size).into())
                }
                _ => panic!("incorrect bitvector size specification"),
            }
        }
        Sort::App(sort_ctor, args) => {
            match sort_ctor {
                SortCtor::Set => {
                    Binding::Variable(
                        ast::Set::new_const(name.display().to_string(), &z3_sort(&args[0], env))
                            .into(),
                    )
                }
                SortCtor::Map => {
                    Binding::Variable(
                        ast::Array::new_const(
                            name.display().to_string(),
                            &z3_sort(&args[0], env),
                            &z3_sort(&args[1], env),
                        )
                        .into(),
                    )
                }
                SortCtor::Data(data_ctor) => {
                    Binding::Variable(
                        ast::Datatype::new_const(
                            name.display().to_string(),
                            env.datatype_lookup(data_ctor).unwrap(),
                        )
                        .into(),
                    )
                }
            }
        }
        &s => panic!("unhandled kind encountered: {:#?}", s),
    }
}

fn z3_sort<T: Types>(s: &Sort<T>, env: &Env<T>) -> z3::Sort {
    match s {
        Sort::Int => z3::Sort::int(),
        Sort::Real => z3::Sort::real(),
        Sort::Bool => z3::Sort::bool(),
        Sort::Str => z3::Sort::string(),
        Sort::BitVec(bv_size) => {
            match **bv_size {
                Sort::BvSize(size) => z3::Sort::bitvector(size),
                _ => panic!("incorrect bitvector size specification"),
            }
        }
        Sort::App(sort_ctor, args) => {
            match sort_ctor {
                SortCtor::Set => z3::Sort::set(&z3_sort(&args[0], env)),
                SortCtor::Map => z3::Sort::array(&z3_sort(&args[0], env), &z3_sort(&args[1], env)),
                SortCtor::Data(sort) => env.datatype_lookup(sort).unwrap().clone(),
            }
        }
        _ => panic!("unhandled sort encountered {:#?}", s),
    }
}

pub(crate) fn is_constraint_satisfiable<T: Types>(
    cstr: &Constraint<T>,
    solver: &Solver,
    env: &mut Env<T>,
) -> FixpointStatus<T::Tag> {
    solver.push();
    let res = match cstr {
        Constraint::Pred(pred, tag) => {
            solver.assert(pred_to_z3(pred, env).not());
            if solver.check() == SatResult::Unsat {
                FixpointStatus::Safe(Stats { num_cstr: 1, num_iter: 0, num_chck: 0, num_vald: 0 })
            } else {
                FixpointStatus::Unsafe(
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
                FixpointStatus::Safe(Stats { num_cstr: 0, num_iter: 0, num_chck: 0, num_vald: 0 }),
                |acc, cstr| is_constraint_satisfiable(cstr, solver, env).merge(acc),
            )
        }

        Constraint::ForAll(bind, inner) => {
            env.insert(bind.name.clone(), new_binding(&bind.name, &bind.sort, env));
            solver.assert(pred_to_z3(&bind.pred, env));
            let inner_soln = is_constraint_satisfiable(inner, solver, env);
            env.pop(&bind.name);
            inner_soln
        }
    };
    solver.pop(1);
    res
}
