use std::{collections::HashMap, fmt};

use crate::{
    BinOp, BinRel, Bind, Constant, Constraint, Expr, Identifier, KVarDecl, Pred, Qualifier, Sort,
    SortCtor, Types,
    constraint_with_env::ConstraintWithEnv,
    format,
    sexp::{Atom, ParseError as SexpParseError, Parser as SexpParser, Sexp},
};

#[derive(Debug)]
pub enum ParseError {
    SexpParseError(SexpParseError),
    MalformedSexpError(&'static str),
}

pub struct PT;
impl Types for PT {
    type Sort = String;
    type KVar = String;
    type Var = String;
    type Tag = String;
    type String = String;
}

impl Identifier for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub trait Parseable<T: Types> {
    fn to_kvar(&self, s: &str) -> Result<T::KVar, ParseError>;
    fn to_var(&self, s: &str) -> Result<T::Var, ParseError>;
}

trait FromSexp<PT: Types> {
    fn var(&self, name: &str) -> Result<PT::Var, ParseError>;
    fn kvar(&self, name: &str) -> Result<PT::KVar, ParseError>;
    fn string(&self, s: &str) -> Result<PT::String, ParseError>;

    fn parse_bv_size(&self, sexp: &Sexp) -> Result<Sort<PT>, ParseError> {
        match sexp {
            Sexp::Atom(Atom::S(s)) if s.starts_with("Size") => {
                let maybe_size = s
                    .strip_prefix("Size")
                    .and_then(|sz_str| sz_str.parse::<u32>().ok());
                if let Some(size) = maybe_size {
                    Ok(Sort::BvSize(size))
                } else {
                    Err(ParseError::MalformedSexpError("Could not parse number for bvsize"))
                }
            }
            _ => {
                Err(ParseError::MalformedSexpError(
                    "Expected bitvec size to be in the form Size{\\d+}",
                ))
            }
        }
    }

    fn parse_name(&self, sexp: &Sexp) -> Result<PT::Var, ParseError> {
        let name = match sexp {
            Sexp::Atom(Atom::S(s)) => self.var(s),
            _ => Err(ParseError::MalformedSexpError("Expected bind name to be a string")),
        }?;
        Ok(name)
    }

    fn parse_bind(&self, sexp: &Sexp) -> Result<Bind<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::List(name_and_sort) => {
                        let name = self.parse_name(&name_and_sort[0])?;
                        let sort = parse_sort(&name_and_sort[1])?;
                        let pred = self.parse_pred_inner(&items[1])?;
                        Ok(Bind { name, sort, pred })
                    }
                    _ => {
                        Err(ParseError::MalformedSexpError(
                            "Expected list for name and sort in bind",
                        ))
                    }
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for bind")),
        }
    }

    fn parse_pred_inner(&self, sexp: &Sexp) -> Result<Pred<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "and" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|item| self.parse_pred_inner(item))
                            .collect::<Result<_, _>>()
                            .map(Pred::And)
                    }
                    Sexp::Atom(Atom::S(s)) if s.starts_with("$") => self.parse_kvar(sexp),
                    _ => self.parse_expr_possibly_nested(sexp).map(Pred::Expr),
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for pred")),
        }
    }

    fn parse_kvar(&self, sexp: &Sexp) -> Result<Pred<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                if items.len() < 2 {
                    Err(ParseError::MalformedSexpError(
                        "Kvar application requires at least two elements",
                    ))
                } else {
                    let maybe_strs: Option<Vec<String>> = items
                        .iter()
                        .map(|s| {
                            if let Sexp::Atom(Atom::S(sym)) = s { Some(sym.clone()) } else { None }
                        })
                        .collect();
                    match maybe_strs {
                        Some(strs) => {
                            let kvar = self.kvar(&strs[0])?;
                            let args = strs[1..]
                                .iter()
                                .map(|s| self.var(s))
                                .collect::<Result<Vec<_>, _>>()?;
                            Ok(Pred::KVar(kvar, args))
                        }
                        _ => {
                            Err(ParseError::MalformedSexpError(
                                "Expected all list elements to be strings",
                            ))
                        }
                    }
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for kvar")),
        }
    }

    fn parse_expr_possibly_nested(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        through_nested_list(sexp, |s| self.parse_expr(s))
    }

    fn parse_expr(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "let" => self.parse_let(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "not" => self.parse_not(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "or" => self.parse_or(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "and" => self.parse_and(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "lit" => parse_bitvec(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "-" && items.len() == 2 => self.parse_neg(sexp),
                    Sexp::Atom(Atom::S(s))
                        if matches!(s.as_str(), "+" | "-" | "*" | "/" | "mod") =>
                    {
                        self.parse_binary_op(sexp)
                    }
                    Sexp::Atom(Atom::S(s))
                        if matches!(s.as_str(), "=" | "!=" | "<" | "<=" | ">" | ">=") =>
                    {
                        self.parse_atom(sexp)
                    }
                    Sexp::Atom(Atom::S(s)) if s == "<=>" => self.parse_iff(sexp),
                    Sexp::Atom(Atom::S(s)) if s == "=>" => self.parse_imp(sexp),
                    _ => self.parse_app(sexp),
                }
            }
            Sexp::Atom(Atom::S(s)) => Ok(Expr::Var(self.var(s)?)),
            Sexp::Atom(Atom::Q(s)) => Ok(Expr::Constant(Constant::String(self.string(s)?))),
            Sexp::Atom(Atom::B(b)) => Ok(Expr::Constant(Constant::Boolean(*b))),
            Sexp::Atom(Atom::I(i)) => Ok(Expr::Constant(Constant::Numeral(*i as u128))),
            Sexp::Atom(Atom::F(f)) => Ok(Expr::Constant(Constant::Real(*f as u128))),
        }
    }

    fn parse_neg(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                Ok(Expr::Neg(Box::new(self.parse_expr_possibly_nested(&items[1])?)))
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for neg")),
        }
    }

    fn parse_not(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                Ok(Expr::Not(Box::new(self.parse_expr_possibly_nested(&items[1])?)))
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for \"not\"")),
        }
    }

    fn parse_iff(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "<=>" => {
                        let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                        let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                        Ok(Expr::Iff(Box::new([exp1, exp2])))
                    }
                    _ => Err(ParseError::MalformedSexpError("Expected iff to start with \"<=>\"")),
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for iff")),
        }
    }

    fn parse_imp(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "=>" => {
                        let exp1 = self.parse_expr_possibly_nested(&items[1])?;
                        let exp2 = self.parse_expr_possibly_nested(&items[2])?;
                        Ok(Expr::Imp(Box::new([exp1, exp2])))
                    }
                    _ => Err(ParseError::MalformedSexpError("Expected imp to start with \"=>\"")),
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for implication")),
        }
    }

    fn parse_and(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "and" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|sexp| self.parse_expr_possibly_nested(sexp))
                            .collect::<Result<_, _>>()
                            .map(Expr::And)
                    }
                    _ => {
                        Err(ParseError::MalformedSexpError(
                            "Expected \"and\" expression to start with \"and\"",
                        ))
                    }
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for \"and\"")),
        }
    }

    fn parse_or(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                match &items[0] {
                    Sexp::Atom(Atom::S(s)) if s == "or" => {
                        items[1..]
                            .to_vec()
                            .iter()
                            .map(|sexp| self.parse_expr_possibly_nested(sexp))
                            .collect::<Result<_, _>>()
                            .map(Expr::Or)
                    }
                    _ => {
                        Err(ParseError::MalformedSexpError(
                            "Expected \"or\" expression to start with \"or\"",
                        ))
                    }
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for \"or\"")),
        }
    }

    fn parse_atom(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
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
                    _ => Err(ParseError::MalformedSexpError("Unsupported atom")),
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for atom")),
        }
    }

    fn parse_app(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
        match sexp {
            Sexp::List(items) => {
                let exp1 = self.parse_expr_possibly_nested(&items[0])?;
                let args: Vec<Expr<PT>> = items[1..]
                    .to_vec()
                    .iter()
                    .map(|sexp| self.parse_expr_possibly_nested(sexp))
                    .collect::<Result<_, _>>()?;
                Ok(Expr::App(Box::new(exp1), args))
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for app")),
        }
    }

    fn parse_binary_op(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
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
                    _ => Err(ParseError::MalformedSexpError("Unsupported atom")),
                }
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for binary operation")),
        }
    }
    fn parse_let(&self, sexp: &Sexp) -> Result<Expr<PT>, ParseError> {
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
                                    let var = self.var(s)?;
                                    Ok(Expr::Let(var, Box::new([binding, body])))
                                }
                                _ => {
                                    Err(ParseError::MalformedSexpError(
                                        "Expected variable name to be string",
                                    ))
                                }
                            }
                        }
                        _ => {
                            Err(ParseError::MalformedSexpError("Expected list for var and binding"))
                        }
                    }
                })
            }
            _ => Err(ParseError::MalformedSexpError("Expected list for let")),
        }
    }
}

fn parse_sort<T: Types>(sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    match sexp {
        Sexp::List(_items) => parse_list_sort(sexp),
        Sexp::Atom(Atom::S(s)) if s == "Int" || s == "int" => Ok(Sort::Int),
        Sexp::Atom(Atom::S(s)) if s == "Bool" || s == "bool" => Ok(Sort::Bool),
        Sexp::Atom(Atom::S(s)) if s == "Real" || s == "real" => Ok(Sort::Real),
        Sexp::Atom(Atom::S(s)) if s == "Str" || s == "str" => Ok(Sort::Str),
        Sexp::Atom(Atom::S(s)) if s.starts_with("Size") => parse_bv_size(sexp),
        // Sexp::Atom(Atom::S(ref s)) => Ok(Sort::Var(s.clone())),
        _ => Err(ParseError::MalformedSexpError("Unknown sort encountered")),
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
                Err(ParseError::MalformedSexpError("Could not parse number for bvsize"))
            }
        }
        _ => {
            Err(ParseError::MalformedSexpError("Expected bitvec size to be in the form Size{\\d+}"))
        }
    }
}

fn parse_func_sort<T: Types>(_sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    Err(ParseError::MalformedSexpError("Func sort hole"))
}

fn parse_bitvec_sort<T: Types>(sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    match sexp {
        Sexp::List(items) if items.len() == 2 => {
            let bitvec_size = parse_bv_size(&items[1])?;
            Ok(Sort::BitVec(Box::new(bitvec_size)))
        }
        _ => Err(ParseError::MalformedSexpError("Expected list of length 2 for bitvec sort")),
    }
}

fn parse_list_sort<T: Types>(sexp: &Sexp) -> Result<Sort<T>, ParseError> {
    match sexp {
        Sexp::List(items) => {
            let args = items[1..]
                .to_vec()
                .iter()
                .map(parse_sort)
                .collect::<Result<Vec<Sort<T>>, ParseError>>()?;
            match &items[0] {
                Sexp::Atom(Atom::S(s)) if s == "func" => parse_func_sort(sexp),
                Sexp::Atom(Atom::S(s)) if s == "Set_Set" && args.len() == 1 => {
                    Ok(Sort::App(SortCtor::Set, args))
                }
                Sexp::Atom(Atom::S(s)) if s == "Map_t" && args.len() == 2 => {
                    Ok(Sort::App(SortCtor::Map, args))
                }
                Sexp::Atom(Atom::S(s)) if s == "BitVec" && args.len() == 1 => {
                    parse_bitvec_sort(sexp)
                }
                _ => Err(ParseError::MalformedSexpError("Unexpected sort constructor encountered")),
            }
        }
        _ => Err(ParseError::MalformedSexpError("Expected list for func or app sort")),
    }
}

fn size_form_bv_sort(sort: Sort<PT>) -> Result<u32, ParseError> {
    match sort {
        Sort::BitVec(ref bv_size_box) => {
            match **bv_size_box {
                Sort::BvSize(size) => Ok(size),
                _ => Err(ParseError::MalformedSexpError("BitVec sort should contain BvSize sort")),
            }
        }
        _ => Err(ParseError::MalformedSexpError("Expected BitVec variant to be provided")),
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
                _ => Err(ParseError::MalformedSexpError("Expected binary literal for bitvec")),
            }
        }
        _ => Err(ParseError::MalformedSexpError("Expected list for bitvector literal")),
    }
}

fn through_nested_list<T, F>(sexp: &Sexp, at_bottom: F) -> T
where
    F: Fn(&Sexp) -> T,
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

// fn parse_forall(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(s)) if s == "forall" => {
//                     let bind = todo!("parse_bind(&items[1])?");
//                     let c = sexp_to_constraint_inner(&items[2])?;
//                     Ok(Constraint::ForAll(bind, Box::new(c)))
//                 }
//                 _ => {
//                     Err(ParseError::MalformedSexpError("Expected forall to start with \"forall\""))
//                 }
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for forall expression")),
//     }
// }

// fn parse_conj(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(s)) if s == "and" => {
//                     items[1..]
//                         .to_vec()
//                         .iter()
//                         .map(sexp_to_constraint_inner)
//                         .collect::<Result<_, _>>()
//                         .map(Constraint::Conj)
//                 }
//                 _ => {
//                     Err(ParseError::MalformedSexpError("Expected conjuction to start with \"and\""))
//                 }
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for constraint conjunction")),
//     }
// }
// fn parse_tagged_pred(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[2] {
//                 Sexp::Atom(Atom::Q(s)) => {
//                     let pred = todo!("parse_pred_inner(&items[1])?");
//                     Ok(Constraint::Pred(pred, Some(s.clone())))
//                 }
//                 _ => Err(ParseError::MalformedSexpError("Expected quoted string for tag")),
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for tagged predicate")),
//     }
// }

// fn parse_pred(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     if let Sexp::List(items) = sexp
//         && let Sexp::Atom(Atom::S(s)) = &items[0]
//         && s == "tag"
//     {
//         return parse_tagged_pred(sexp);
//     }
//     let pred = todo!("parse_pred_inner(sexp)?");
//     Ok(Constraint::Pred(pred, None))
// }

// fn sexp_to_constraint_inner(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(s)) if s == "forall" => parse_forall(sexp),
//                 Sexp::Atom(Atom::S(s)) if s == "and" => parse_conj(sexp),
//                 _ => parse_pred(sexp),
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected constraint body to be list")),
//     }
// }

// fn sexp_to_constraint(sexp: &Sexp) -> Result<Constraint<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(atom)) if atom == "constraint" => {
//                     sexp_to_constraint_inner(&items[1])
//                 }
//                 _ => {
//                     Err(ParseError::MalformedSexpError(
//                         "Expected constraint definition to start with \"constraint\"",
//                     ))
//                 }
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for constraint definition")),
//     }
// }

// fn parse_kvar_decl_args(sexp: &Sexp) -> Result<Vec<Sort<PT>>, ParseError> {
//     match sexp {
//         Sexp::List(items) => items.iter().map(parse_sort).collect(),
//         _ => Err(ParseError::MalformedSexpError("Expected list of sorts for kvar declaration")),
//     }
// }

// fn sexp_to_kvar_decl_inner(sexp: &Sexp) -> Result<KVarDecl<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[1] {
//                 Sexp::Atom(Atom::S(s)) if s.starts_with("$") => {
//                     let sorts = parse_kvar_decl_args(&items[2])?;
//                     Ok(KVarDecl { kvid: s.clone(), sorts, comment: String::new() })
//                 }
//                 _ => Err(ParseError::MalformedSexpError("Expected kvar name to start with $")),
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for kvar declaration")),
//     }
// }

// fn sexp_to_kvar_decl(sexp: &Sexp) -> Result<KVarDecl<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(atom)) if atom == "var" => sexp_to_kvar_decl_inner(sexp),
//                 _ => {
//                     Err(ParseError::MalformedSexpError(
//                         "Expected kvar declaration to start with \"var\"",
//                     ))
//                 }
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for constraint definition")),
//     }
// }

// fn parse_qualifier_arg(sexp: &Sexp) -> Result<(String, Sort<PT>), ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             if let Sexp::Atom(Atom::S(var_name)) = &items[0] {
//                 let arg_sort = parse_sort(&items[1])?;
//                 Ok((var_name.clone(), arg_sort))
//             } else {
//                 Err(ParseError::MalformedSexpError(
//                     "Expected qualifier argument to have variable name",
//                 ))
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for qualifier argument")),
//     }
// }

// fn parse_qualifier_args(sexp: &Sexp) -> Result<Vec<(String, Sort<PT>)>, ParseError> {
//     match sexp {
//         Sexp::List(args) => args.iter().map(parse_qualifier_arg).collect(),
//         _ => Err(ParseError::MalformedSexpError("Expected list for qualifier arguments")),
//     }
// }

// fn sexp_to_qualifier_inner(sexp: &Sexp) -> Result<Qualifier<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             if let Sexp::Atom(Atom::S(name)) = &items[1] {
//                 let qualifier_args = parse_qualifier_args(&items[2])?;
//                 let qualifier_body = parse_expr_possibly_nested(&items[3])?;
//                 Ok(Qualifier { name: name.clone(), args: qualifier_args, body: qualifier_body })
//             } else {
//                 Err(ParseError::MalformedSexpError(
//                     "Expected qualifier declaration to provide name",
//                 ))
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for qualifier declaration")),
//     }
// }

// fn sexp_to_qualifier(sexp: &Sexp) -> Result<Qualifier<PT>, ParseError> {
//     match sexp {
//         Sexp::List(items) => {
//             match &items[0] {
//                 Sexp::Atom(Atom::S(atom)) if atom == "qualif" => sexp_to_qualifier_inner(sexp),
//                 _ => {
//                     Err(ParseError::MalformedSexpError(
//                         "Expected qualifier declaration to start with \"qualif\"",
//                     ))
//                 }
//             }
//         }
//         _ => Err(ParseError::MalformedSexpError("Expected list for qualifier declaration")),
//     }
// }

// pub fn parse_constraint(input: &str) -> Result<Constraint<ParsingTypes>, ParseError> {
//     let mut sexp_parser = SexpParser::new(input);
//     let sexp = sexp_parser.parse().map_err(ParseError::SexpParseError)?;
//     sexp_to_constraint(&sexp)
// }

// pub fn parse_constraint_with_kvars(input: &str) -> Result<ConstraintWithEnv<PT>, ParseError> {
//     let mut sexp_parser = SexpParser::new(input);
//     let sexps = sexp_parser
//         .parse_all()
//         .map_err(ParseError::SexpParseError)?;
//     let mut kvar_decls = Vec::new();
//     let mut qualifiers = Vec::new();
//     for sexp in sexps {
//         if let Ok(kvar_decl) = sexp_to_kvar_decl(&sexp) {
//             kvar_decls.push(kvar_decl);
//         } else if let Ok(qualifier) = sexp_to_qualifier(&sexp) {
//             qualifiers.push(qualifier);
//         } else if let Ok(constraint) = sexp_to_constraint(&sexp) {
//             return Ok(ConstraintWithEnv::new(vec![], kvar_decls, qualifiers, vec![], constraint));
//         }
//     }
//     Err(ParseError::MalformedSexpError("No constraint found"))
// }
