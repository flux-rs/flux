use std::fmt;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    BinOp, BinRel, Bind, Constant, Expr, Identifier, Pred, Sort, SortCtor, ThyFunc, Types,
    constraint::BoundVar,
    sexp::{Atom, ParseError as SexpParseError, Sexp},
};

#[derive(Debug)]
pub enum ParseError {
    SexpParseError(SexpParseError),
    MalformedSexpError(String),
}

impl ParseError {
    pub fn err(msg: impl Into<String>) -> Self {
        ParseError::MalformedSexpError(msg.into())
    }
}

impl Identifier for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub trait FromSexp<T: Types> {
    // These are the only methods required to implement FromSexp
    fn var(&self, name: &str) -> Result<T::Var, ParseError>;
    fn kvar(&self, name: &str) -> Result<T::KVar, ParseError>;
    fn string(&self, s: &str) -> Result<T::String, ParseError>;
    fn sort(&self, name: &str) -> Result<T::Sort, ParseError>;
    fn into_wrapper(self) -> FromSexpWrapper<T, Self>
    where
        Self: Sized,
    {
        FromSexpWrapper { parser: self, _phantom: std::marker::PhantomData, scopes: vec![] }
    }
}

pub struct FromSexpWrapper<T: Types, Parser> {
    pub parser: Parser,
    pub _phantom: std::marker::PhantomData<T>,
    scopes: Vec<IndexSet<String>>,
}

type KvarSolution<T> = (Vec<Sort<T>>, Expr<T>);

impl<T, Parser: FromSexp<T>> FromSexpWrapper<T, Parser>
where
    T: Types,
{
    fn parse_bv_size(&self, sexp: &Sexp) -> Result<Sort<T>, ParseError> {
        match sexp {
            Sexp::Atom(Atom::S(s)) if s.starts_with("Size") => {
                let maybe_size = s
                    .strip_prefix("Size")
                    .and_then(|sz_str| sz_str.parse::<u32>().ok());
                if let Some(size) = maybe_size {
                    Ok(Sort::BvSize(size))
                } else {
                    Err(ParseError::err("Could not parse number for bvsize"))
                }
            }
            _ => Err(ParseError::err("Expected bitvec size to be in the form Size{\\d+}")),
        }
    }

    pub fn parse_name(&self, sexp: &Sexp) -> Result<T::Var, ParseError> {
        let name = match sexp {
            Sexp::Atom(Atom::S(s)) => self.parser.var(s),
            _ => Err(ParseError::err("Expected bind name to be a string")),
        }?;
        Ok(name)
    }

    pub fn parse_bind(&mut self, sexp: &Sexp) -> Result<Bind<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::List(name_and_sort) => {
                        let name = self.parse_name(&name_and_sort[0])?;
                        let sort = self.parse_sort(&name_and_sort[1])?;
                        let pred = self.parse_pred_inner(&items[1])?;
                        Ok(Bind { name, sort, pred })
                    }
                    _ => Err(ParseError::err("Expected list for name and sort in bind")),
                }
            }
            _ => Err(ParseError::err("Expected list for bind")),
        }
    }

    fn parse_pred_inner(&mut self, sexp: &Sexp) -> Result<Pred<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "and" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|item| self.parse_pred_inner(item))
                            .try_collect()
                            .map(Pred::And)
                    }
                    Sexp::Atom(Atom::S(s)) if s.starts_with("$") => self.parse_kvar(sexp),
                    _ => self.parse_expr_possibly_nested(sexp).map(Pred::Expr),
                }
            }
            _ => Err(ParseError::err("Expected list for pred")),
        }
    }

    pub fn parse_kvar(&self, sexp: &Sexp) -> Result<Pred<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                if items.len() < 2 {
                    Err(ParseError::err("Kvar application requires at least two elements"))
                } else {
                    let maybe_strs: Option<Vec<String>> = items
                        .iter()
                        .map(|s| {
                            if let Sexp::Atom(Atom::S(sym)) = s { Some(sym.clone()) } else { None }
                        })
                        .collect();
                    match maybe_strs {
                        Some(strs) => {
                            let kvar = self.parser.kvar(&strs[0])?;
                            let mut args = vec![];
                            for s in &strs[1..] {
                                args.push(Expr::Var(self.parser.var(s)?));
                            }
                            Ok(Pred::KVar(kvar, args))
                        }
                        _ => Err(ParseError::err("Expected all list elements to be strings")),
                    }
                }
            }
            _ => Err(ParseError::err("Expected list for kvar")),
        }
    }

    fn parse_expr_possibly_nested(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        through_nested_list(sexp, |s| self.parse_expr(s))
    }

    fn parse_is_ctor(&mut self, ctor_name: &str, arg: &Sexp) -> Result<Expr<T>, ParseError> {
        let ctor = self.parser.var(ctor_name)?;
        let arg = self.parse_expr(arg)?;
        Ok(Expr::IsCtor(ctor, Box::new(arg)))
    }

    pub fn parse_expr(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                if let Sexp::Atom(Atom::S(s)) = &items[0] {
                    match s.as_str() {
                        "exists" => self.parse_exists(&items[1..]),
                        "let" => self.parse_let(sexp),
                        "not" => self.parse_not(sexp),
                        "or" => self.parse_or(sexp),
                        "and" => self.parse_and(sexp),
                        "lit" => parse_bitvec(sexp),
                        "-" if items.len() == 2 => self.parse_neg(sexp),
                        "+" | "-" | "*" | "/" | "mod" => self.parse_binary_op(sexp),
                        "=" | "!=" | "<" | "<=" | ">" | ">=" => self.parse_atom(sexp),
                        "<=>" => self.parse_iff(sexp),
                        "=>" => self.parse_imp(sexp),
                        "cast_as_int" => self.parse_expr(&items[1]), // some odd thing that fixpoint-hs seems to add for sets...
                        _ if s.starts_with("is$") => self.parse_is_ctor(&s[3..], &items[1]),
                        _ => self.parse_app(sexp),
                    }
                } else {
                    self.parse_app(sexp)
                }
            }
            Sexp::Atom(Atom::S(s)) => {
                if let Some(thy_func) = parse_thy_func(s) {
                    Ok(Expr::ThyFunc(thy_func))
                } else if let Some(bv) = self.parse_bound_var(s) {
                    Ok(bv)
                } else {
                    Ok(Expr::Var(self.parser.var(s)?))
                }
            }
            Sexp::Atom(Atom::Q(s)) => Ok(Expr::Constant(Constant::String(self.parser.string(s)?))),
            Sexp::Atom(Atom::B(b)) => Ok(Expr::Constant(Constant::Boolean(*b))),
            Sexp::Atom(Atom::I(i)) => Ok(Expr::Constant(Constant::Numeral(*i as u128))),
            Sexp::Atom(Atom::F(f)) => Ok(Expr::Constant(Constant::Real(*f as u128))),
        }
    }

    fn parse_neg(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                Ok(Expr::Neg(Box::new(self.parse_expr_possibly_nested(&items[1])?)))
            }
            _ => Err(ParseError::err("Expected list for neg")),
        }
    }

    fn parse_not(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                Ok(Expr::Not(Box::new(self.parse_expr_possibly_nested(&items[1])?)))
            }
            _ => Err(ParseError::err("Expected list for \"not\"")),
        }
    }

    fn parse_iff(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "<=>" => {
                        let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                        let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                        Ok(Expr::Iff(Box::new([exp1, exp2])))
                    }
                    _ => Err(ParseError::err("Expected iff to start with \"<=>\"")),
                }
            }
            _ => Err(ParseError::err("Expected list for iff")),
        }
    }

    fn parse_imp(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "=>" => {
                        let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                        let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                        Ok(Expr::Imp(Box::new([exp1, exp2])))
                    }
                    _ => Err(ParseError::err("Expected imp to start with \"=>\"")),
                }
            }
            _ => Err(ParseError::err("Expected list for implication")),
        }
    }

    fn parse_and(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "and" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|sexp| self.parse_expr_possibly_nested(sexp))
                            .try_collect()
                            .map(Expr::And)
                    }
                    _ => Err(ParseError::err("Expected \"and\" expression to start with \"and\"")),
                }
            }
            _ => Err(ParseError::err("Expected list for \"and\"")),
        }
    }

    fn parse_or(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "or" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|sexp| self.parse_expr_possibly_nested(sexp))
                            .try_collect()
                            .map(Expr::Or)
                    }
                    _ => Err(ParseError::err("Expected \"or\" expression to start with \"or\"")),
                }
            }
            _ => Err(ParseError::err("Expected list for \"or\"")),
        }
    }

    fn parse_atom(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                let exp_pair = Box::new([exp1, exp2]);
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "=" => Ok(Expr::Atom(BinRel::Eq, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "!=" => Ok(Expr::Atom(BinRel::Ne, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "<=" => Ok(Expr::Atom(BinRel::Le, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "<" => Ok(Expr::Atom(BinRel::Lt, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == ">=" => Ok(Expr::Atom(BinRel::Ge, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == ">" => Ok(Expr::Atom(BinRel::Gt, exp_pair)),
                    _ => Err(ParseError::err("Unsupported atom")),
                }
            }
            _ => Err(ParseError::err("Expected list for atom")),
        }
    }

    fn parse_app(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                let exp1 = self.parse_expr_possibly_nested(&items[0])?;
                let args: Vec<Expr<T>> = items[1..]
                    .to_vec()
                    .iter()
                    .map(|sexp| self.parse_expr_possibly_nested(sexp))
                    .try_collect()?;
                Ok(Expr::App(Box::new(exp1), None, args))
            }
            _ => Err(ParseError::err("Expected list for app")),
        }
    }

    fn parse_binary_op(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                let exp_pair = Box::new([exp1, exp2]);
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "+" => Ok(Expr::BinaryOp(BinOp::Add, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "-" => Ok(Expr::BinaryOp(BinOp::Sub, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "*" => Ok(Expr::BinaryOp(BinOp::Mul, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "/" => Ok(Expr::BinaryOp(BinOp::Div, exp_pair)),
                    Sexp::Atom(Atom::S(s)) if s == "mod" => {
                        Ok(Expr::BinaryOp(BinOp::Mod, exp_pair))
                    }
                    _ => Err(ParseError::err("Unsupported atom")),
                }
            }
            _ => Err(ParseError::err("Expected list for binary operation")),
        }
    }
    fn parse_exists(&mut self, items: &[Sexp]) -> Result<Expr<T>, ParseError> {
        let [Sexp::List(var_sorts), body] = items else {
            return Err(ParseError::err("Expected list for vars and sorts in exists"));
        };
        let mut names = Vec::new();
        let mut sorts = Vec::new();
        for var_sort in var_sorts {
            if let Sexp::List(items) = var_sort
                && let [var, sort] = &items[..]
            {
                let Sexp::Atom(Atom::S(name)) = var else {
                    return Err(ParseError::err("Expected variable name to be string {var:?}"));
                };
                names.push(name.clone());
                sorts.push(self.parse_sort(sort)?);
            } else {
                return Err(ParseError::err(format!(
                    "Expected list for var and sort in exists {var_sort:?}"
                )));
            }
        }
        self.push_scope(&names);
        let body = self.parse_expr_possibly_nested(body)?;
        self.pop_scope();
        Ok(Expr::Exists(sorts, Box::new(body)))
    }

    fn parse_let(&mut self, sexp: &Sexp) -> Result<Expr<T>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                through_nested_list(&items[1], |bottom| {
                    match bottom {
                        Sexp::List(var_and_binding) => {
                            match &var_and_binding[0] {
                                Sexp::Atom(Atom::S(s)) => {
                                    let binding =
                                        self.parse_expr_possibly_nested(&var_and_binding[1])?;
                                    let body = self.parse_expr_possibly_nested(&items[2])?;
                                    let var = self.parser.var(s)?;
                                    Ok(Expr::Let(var, Box::new([binding, body])))
                                }
                                _ => Err(ParseError::err("Expected variable name to be string")),
                            }
                        }
                        _ => Err(ParseError::err("Expected list for var and binding")),
                    }
                })
            }
            _ => Err(ParseError::err("Expected list for let")),
        }
    }

    fn parse_list_sort(&self, sexp: &Sexp) -> Result<Sort<T>, ParseError> {
        let Sexp::List(items) = sexp else {
            return Err(ParseError::err("Expected list for func or app sort"));
        };
        if items.is_empty() {
            return Err(ParseError::err("Empty list encountered when parsing sort"));
        }
        let Sexp::Atom(Atom::S(ctor)) = &items[0] else {
            return Err(ParseError::err("Unexpected sort constructor encountered"));
        };
        if ctor == "func" && items.len() == 4 {
            return self.parse_func_sort(&items[1..]);
        }
        if ctor == "function" && items.len() == 3 {
            let input = self.parse_sort(&items[1])?;
            let output = self.parse_sort(&items[2])?;
            return Ok(Sort::mk_func(0, vec![input], output));
        }
        let args: Vec<_> = items[1..]
            .to_vec()
            .iter()
            .map(|sexp| self.parse_sort(sexp))
            .try_collect()?;
        if ctor == "Set_Set" && args.len() == 1 {
            return Ok(Sort::App(SortCtor::Set, args));
        }
        if (ctor == "Map_t") && args.len() == 2 {
            return Ok(Sort::App(SortCtor::Map, args));
        }
        if ctor == "BitVec" && args.len() == 1 {
            return parse_bitvec_sort(sexp);
        }
        let ctor = SortCtor::Data(self.parser.sort(ctor)?);
        Ok(Sort::App(ctor, args))
    }

    pub fn parse_sort(&self, sexp: &Sexp) -> Result<Sort<T>, ParseError> {
        match sexp {
            Sexp::List(_items) => self.parse_list_sort(sexp),
            Sexp::Atom(Atom::S(s)) => {
                if s == "Int" || s == "int" {
                    Ok(Sort::Int)
                } else if s == "Bool" || s == "bool" {
                    Ok(Sort::Bool)
                } else if s == "Real" || s == "real" {
                    Ok(Sort::Real)
                } else if s == "Str" || s == "str" {
                    Ok(Sort::Str)
                } else if s.starts_with("Size") {
                    self.parse_bv_size(sexp)
                } else {
                    let ctor = SortCtor::Data(self.parser.sort(s)?);
                    Ok(Sort::App(ctor, vec![]))
                }
            }
            // Sexp::Atom(Atom::S(ref s)) => Ok(Sort::Var(s.clone())),
            _ => panic!("Unknown sort encountered {sexp:?}"), // Err(ParseError::err(format!("Unknown sort encountered {sexp:?}"))),
        }
    }

    fn parse_func_sort(&self, items: &[Sexp]) -> Result<Sort<T>, ParseError> {
        if let Sexp::Atom(Atom::I(params)) = &items[0]
            && *params >= 0
            && let Sexp::List(inputs) = &items[1]
        {
            let params = *params as usize;
            let inputs: Vec<_> = inputs
                .iter()
                .map(|sexp| self.parse_sort(sexp))
                .try_collect()?;
            let output = self.parse_sort(&items[2])?;
            Ok(Sort::mk_func(params, inputs, output))
        } else {
            Err(ParseError::err("Expected arity to be an integer"))
        }
    }

    pub fn parse_solution(&mut self, sexp: &Sexp) -> Result<KvarSolution<T>, ParseError> {
        if let Sexp::List(items) = sexp
            && let [_lambda, params, body] = &items[..]
            && let Sexp::List(sexp_params) = params
        {
            let mut kvar_args = vec![];
            let mut sorts = vec![];

            for param in sexp_params {
                if let Sexp::List(bind) = param
                    && let [_name, sort] = &bind[..]
                    && let Sexp::Atom(Atom::S(s)) = _name
                {
                    kvar_args.push(s.clone());
                    sorts.push(sort);
                } else {
                    return Err(ParseError::err("expected parameter names to be symbols"));
                }
            }
            let sorts = sorts
                .into_iter()
                .map(|sexp| self.parse_sort(sexp))
                .try_collect()?;
            self.push_scope(&kvar_args);

            let expr = self.parse_expr(body)?;
            Ok((sorts, expr))
        } else {
            Err(ParseError::err("expected (lambda (params) body)"))
        }
    }

    fn push_scope(&mut self, names: &[String]) {
        self.scopes.push(names.iter().cloned().collect());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn parse_bound_var(&self, name: &str) -> Option<Expr<T>> {
        for (level, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(idx) = scope.get_index_of(name) {
                return Some(Expr::BoundVar(BoundVar { level, idx }));
            }
        }
        None
    }
}

fn parse_bv_size<T: Types>(sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    match sexp {
        Sexp::Atom(Atom::S(s)) if s.starts_with("Size") => {
            let maybe_size = s
                .strip_prefix("Size")
                .and_then(|sz_str| sz_str.parse::<u32>().ok());
            if let Some(size) = maybe_size {
                Ok(Sort::BvSize(size))
            } else {
                Err(ParseError::err("Could not parse number for bvsize"))
            }
        }
        _ => Err(ParseError::err("Expected bitvec size to be in the form Size{\\d+}")),
    }
}

fn parse_bitvec_sort<T: Types>(sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    match sexp {
        Sexp::List(items) if items.len() == 2 => {
            let bitvec_size = parse_bv_size(&items[1])?;
            Ok(Sort::BitVec(Box::new(bitvec_size)))
        }
        _ => Err(ParseError::err("Expected list of length 2 for bitvec sort")),
    }
}

fn size_form_bv_sort(sort: Sort<StringTypes>) -> Result<u32, ParseError> {
    match sort {
        Sort::BitVec(ref bv_size_box) => {
            match **bv_size_box {
                Sort::BvSize(size) => Ok(size),
                _ => Err(ParseError::err("BitVec sort should contain BvSize sort")),
            }
        }
        _ => Err(ParseError::err("Expected BitVec variant to be provided")),
    }
}

fn parse_bitvec<PT: Types>(sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
    match sexp {
        Sexp::List(items) => {
            match &items[1] {
                Sexp::Atom(Atom::Q(lit)) if lit.starts_with("#b") => {
                    let bitvec = u128::from_str_radix(&lit[3..], 2).expect("Invalid binary string");
                    let bvsize = size_form_bv_sort(parse_bitvec_sort(&items[2])?)?;
                    Ok(Expr::Constant(Constant::BitVec(bitvec, bvsize)))
                }
                _ => Err(ParseError::err("Expected binary literal for bitvec")),
            }
        }
        _ => Err(ParseError::err("Expected list for bitvector literal")),
    }
}

fn parse_thy_func(name: &str) -> Option<ThyFunc> {
    match name {
        // STRINGS
        "strLen" => Some(ThyFunc::StrLen),

        // BIT VECTORS - conversions
        "int_to_bv8" => Some(ThyFunc::IntToBv8),
        "bv8_to_int" => Some(ThyFunc::Bv8ToInt),
        "int_to_bv32" => Some(ThyFunc::IntToBv32),
        "bv32_to_int" => Some(ThyFunc::Bv32ToInt),
        "int_to_bv64" => Some(ThyFunc::IntToBv64),
        "bv64_to_int" => Some(ThyFunc::Bv64ToInt),

        // BIT VECTORS - comparisons
        "bvule" => Some(ThyFunc::BvUle),
        "bvsle" => Some(ThyFunc::BvSle),
        "bvuge" => Some(ThyFunc::BvUge),
        "bvsge" => Some(ThyFunc::BvSge),
        "bvugt" => Some(ThyFunc::BvUgt),
        "bvsgt" => Some(ThyFunc::BvSgt),
        "bvult" => Some(ThyFunc::BvUlt),
        "bvslt" => Some(ThyFunc::BvSlt),

        // BIT VECTORS - arithmetic/logical operations
        "bvudiv" => Some(ThyFunc::BvUdiv),
        "bvsdiv" => Some(ThyFunc::BvSdiv),
        "bvurem" => Some(ThyFunc::BvUrem),
        "bvsrem" => Some(ThyFunc::BvSrem),
        "bvlshr" => Some(ThyFunc::BvLshr),
        "bvashr" => Some(ThyFunc::BvAshr),
        "bvand" => Some(ThyFunc::BvAnd),
        "bvor" => Some(ThyFunc::BvOr),
        "bvxor" => Some(ThyFunc::BvXor),
        "bvnot" => Some(ThyFunc::BvNot),
        "bvadd" => Some(ThyFunc::BvAdd),
        "bvneg" => Some(ThyFunc::BvNeg),
        "bvsub" => Some(ThyFunc::BvSub),
        "bvmul" => Some(ThyFunc::BvMul),
        "bvshl" => Some(ThyFunc::BvShl),

        // SETS
        "Set_empty" => Some(ThyFunc::SetEmpty),
        "Set_sng" => Some(ThyFunc::SetSng),
        "Set_cup" => Some(ThyFunc::SetCup),
        "Set_cap" => Some(ThyFunc::SetCap),
        "Set_dif" => Some(ThyFunc::SetDif),
        "Set_mem" => Some(ThyFunc::SetMem),
        "Set_sub" => Some(ThyFunc::SetSub),

        // MAPS
        "Map_default" => Some(ThyFunc::MapDefault),
        "Map_select" | "arr_select_m" => Some(ThyFunc::MapSelect),
        "Map_store" | "arr_store_m" => Some(ThyFunc::MapStore),

        // Note: BvZeroExtend and BvSignExtend have parametric forms like "app (_ zero_extend N)"
        // These would need special parsing in the caller
        _ => None,
    }
}

fn through_nested_list<T, F>(sexp: &Sexp, mut at_bottom: F) -> T
where
    F: FnMut(&Sexp) -> T,
{
    let mut current = sexp;
    while let Sexp::List(items) = current {
        if items.len() == 1 {
            current = &items[0];
        } else {
            break;
        }
    }
    at_bottom(current)
}

/// Trivial implementation of Types using `String` for all associated types -----------------------------------
pub struct StringTypes;
impl Types for StringTypes {
    type Sort = String;
    type KVar = String;
    type Var = String;
    type Tag = String;
    type String = String;
}

impl FromSexp<StringTypes> for StringTypes {
    fn var(&self, name: &str) -> Result<String, ParseError> {
        Ok(name.to_string())
    }

    fn kvar(&self, name: &str) -> Result<String, ParseError> {
        Ok(name.to_string())
    }

    fn string(&self, s: &str) -> Result<String, ParseError> {
        Ok(s.to_string())
    }

    fn sort(&self, name: &str) -> Result<String, ParseError> {
        Ok(name.to_string())
    }
}
