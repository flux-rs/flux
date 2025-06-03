use std::sync::LazyLock;
use std::str::FromStr;
use std::marker::PhantomData;
use std::fmt;

use derive_where::derive_where;
use serde::{
    de::{self, Deserializer, Visitor, MapAccess},
    Deserialize, Serialize,
};

// Use items from crate root
use crate::{Types, DefaultTypes};


pub(crate) static DEFAULT_QUALIFIERS: LazyLock<[Qualifier<DefaultTypes>; 11]> =
    LazyLock::new(|| {
        let v_var: <DefaultTypes as Types>::Var = "v".to_string();
        let a_var: <DefaultTypes as Types>::Var = "a".to_string();
        let b_var: <DefaultTypes as Types>::Var = "b".to_string();

        let eqzero = Qualifier {
            args: vec![(v_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var(v_var.clone()), Expr::int(0)])),
            name: String::from("EqZero"),
        };
        let gtzero = Qualifier {
            args: vec![(v_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var(v_var.clone()), Expr::int(0)])),
            name: String::from("GtZero"),
        };
        let gezero = Qualifier {
            args: vec![(v_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var(v_var.clone()), Expr::int(0)])),
            name: String::from("GeZero"),
        };
        let ltzero = Qualifier {
            args: vec![(v_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var(v_var.clone()), Expr::int(0)])),
            name: String::from("LtZero"),
        };
        let lezero = Qualifier {
            args: vec![(v_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var(v_var.clone()), Expr::int(0)])),
            name: String::from("LeZero"),
        };
        let eq = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var(a_var.clone()), Expr::Var(b_var.clone())])),
            name: String::from("Eq"),
        };
        let gt = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var(a_var.clone()), Expr::Var(b_var.clone())])),
            name: String::from("Gt"),
        };
        let ge = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var(a_var.clone()), Expr::Var(b_var.clone())])),
            name: String::from("Ge"),
        };
        let lt = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var(a_var.clone()), Expr::Var(b_var.clone())])),
            name: String::from("Lt"),
        };
        let le = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var(a_var.clone()), Expr::Var(b_var.clone())])),
            name: String::from("Le"),
        };
        let le1 = Qualifier {
            args: vec![(a_var.clone(), Sort::Int), (b_var.clone(), Sort::Int)],
            body: Expr::Atom(
                BinRel::Le,
                Box::new([
                    Expr::Var(a_var.clone()),
                    Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var(b_var.clone()), Expr::int(1)])),
                ]),
            ),
            name: String::from("Le1"),
        };
        [eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
    });


#[derive_where(Hash, Debug, Clone)]
pub struct Bind<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    pub pred: Pred<T>,
}

#[derive_where(Hash, Debug, Clone)]
pub enum Constraint<T: Types> {
    Pred(Pred<T>, #[derive_where(skip)] Option<T::Tag>),
    Conj(Vec<Self>),
    ForAll(Bind<T>, Box<Self>),
}

impl<T: Types> Constraint<T> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);
    pub fn foralls(bindings: Vec<Bind<T>>, c: Self) -> Self {
        bindings.into_iter().rev().fold(c, |c, bind| Constraint::ForAll(bind, Box::new(c)))
    }
    pub fn conj(mut cstrs: Vec<Self>) -> Self {
        if cstrs.len() == 1 { cstrs.remove(0) } else { Self::Conj(cstrs) }
    }
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::ForAll(_, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
    }
}

#[derive_where(Hash, Debug, Clone)]
pub struct DataDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
    pub ctors: Vec<DataCtor<T>>,
}

#[derive_where(Hash, Debug, Clone)]
pub struct DataCtor<T: Types> {
    pub name: T::Var,
    pub fields: Vec<DataField<T>>,
}

#[derive_where(Hash, Debug, Clone)]
pub struct DataField<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
}

// Added Debug to Sort<T: Types>
#[derive_where(Hash, Clone, Debug)]
// Sort<T> needs T: Debug because of SortCtor which might contain T::Sort
// and T::Sort requires T: Types which requires T: Debug
#[derive(Serialize)] // For FixpointResult if it serializes Sort
pub enum Sort<T: Types> {
    Int,
    Bool,
    Real,
    Str,
    BitVec(Box<Sort<T>>),
    BvSize(u32),
    Var(usize),
    Func(Box<[Self; 2]>),
    Abs(usize, Box<Self>),
    App(SortCtor<T>, Vec<Self>),
}

impl<T: Types> Sort<T> {
    pub fn mk_func<I>(params: usize, inputs: I, output: Sort<T>) -> Sort<T>
    where I: IntoIterator<Item = Sort<T>>, I::IntoIter: DoubleEndedIterator,
    {
        let sort = inputs.into_iter().rev().fold(output, |output, input| Sort::Func(Box::new([input, output])));
        (0..params).rev().fold(sort, |sort, i| Sort::Abs(i, Box::new(sort)))
    }
    pub(crate) fn peel_out_abs(&self) -> (usize, &Sort<T>) {
        let mut n = 0;
        let mut curr = self;
        while let Sort::Abs(i, sort) = curr {
            assert_eq!(*i, n);
            n += 1;
            curr = sort;
        }
        (n, curr)
    }
}

// derive_where does not support Deserialize/Serialize.
// SortCtor<T> needs T: Debug for its own Debug derive if T::Sort is involved.
// T::Sort needs Debug from Types trait.
#[derive_where(Hash, Clone, Debug)]
#[derive(Deserialize, Serialize)]
pub enum SortCtor<T: Types> {
    Set,
    Map,
    Data(T::Sort),
}


#[derive_where(Hash, Debug, Clone)]
pub enum Pred<T: Types> {
    And(Vec<Self>),
    KVar(T::KVar, Vec<T::Var>),
    Expr(Expr<T>),
}

impl<T: Types> Pred<T> {
    pub const TRUE: Self = Pred::Expr(Expr::Constant(Constant::Boolean(true)));
    pub fn and(mut preds: Vec<Self>) -> Self {
        if preds.len() == 1 { preds.remove(0) } else { Self::And(preds) }
    }
    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(Expr::Constant(Constant::Boolean(true))) => true,
            Pred::And(ps) => ps.is_empty(),
            _ => false,
        }
    }
    pub fn is_concrete(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::is_concrete),
            Pred::KVar(_, _) => false,
            Pred::Expr(_) => true,
        }
    }
}

#[derive(Hash, Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)] // Added Deserialize
pub enum BinRel {
    Eq, Ne, Gt, Ge, Lt, Le,
}

impl BinRel {
    pub const INEQUALITIES: [BinRel; 4] = [BinRel::Gt, BinRel::Ge, BinRel::Lt, BinRel::Le];
}

impl FromStr for BinRel {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Eq" => Ok(BinRel::Eq), "Ne" => Ok(BinRel::Ne),
            "Gt" => Ok(BinRel::Gt), "Ge" => Ok(BinRel::Ge),
            "Lt" => Ok(BinRel::Lt), "Le" => Ok(BinRel::Le),
            _ => Err(format!("Unknown BinRel: {}", s)),
        }
    }
}

// Expr<T> needs T: Types + Debug for its own Debug derive.
#[derive_where(Debug, Hash, Clone)]
#[derive(Serialize)]
pub enum Expr<T: Types> { // Removed + Debug here, derive_where will add it
    Constant(Constant<T>),
    Var(T::Var),
    App(Box<Self>, Vec<Self>),
    Neg(Box<Self>),
    BinaryOp(BinOp, Box<[Self; 2]>),
    IfThenElse(Box<[Self; 3]>),
    And(Vec<Self>),
    Or(Vec<Self>),
    Not(Box<Self>),
    Imp(Box<[Self; 2]>),
    Iff(Box<[Self; 2]>),
    Atom(BinRel, Box<[Self; 2]>),
    Let(T::Var, Box<[Self; 2]>),
}

impl<T: Types> From<Constant<T>> for Expr<T> {
    fn from(v: Constant<T>) -> Self { Self::Constant(v) }
}

impl<T: Types> Expr<T> {
    pub const fn int(val: u128) -> Expr<T> {
        Expr::Constant(Constant::Numeral(val))
    }
    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }
    pub fn and(mut exprs: Vec<Self>) -> Self {
        if exprs.len() == 1 { exprs.remove(0) } else { Self::And(exprs) }
    }
}

// Constant<T> needs T: Types + Debug for its own Debug derive.
#[derive_where(Debug, Hash, Clone)]
#[derive(Serialize)]
pub enum Constant<T: Types> { // Removed + Debug here
    Numeral(u128),
    Decimal(T::Decimal),
    Boolean(bool),
    String(T::String),
    BitVec(u128, u32),
}

fn parse_bitvec_literal(s: &str) -> Result<(u128, u32), String> {
    if s.starts_with("#x") {
        let hex_part = &s[2..];
        if hex_part.is_empty() { return Err("Empty hex bitvector".to_string()); }
        if hex_part.len() > 32 { return Err(format!("Hex bitvector too long for u128: {} chars", hex_part.len()));}
        u128::from_str_radix(hex_part, 16)
            .map(|val| (val, hex_part.len() as u32 * 4))
            .map_err(|e| format!("Failed to parse hex bitvector: {} ({})", s, e))
    } else if s.starts_with("#b") {
        let bin_part = &s[2..];
        if bin_part.is_empty() { return Err("Empty binary bitvector".to_string()); }
        if bin_part.len() > 128 { return Err(format!("Binary bitvector too long for u128: {} bits", bin_part.len()));}
        u128::from_str_radix(bin_part, 2)
            .map(|val| (val, bin_part.len() as u32))
            .map_err(|e| format!("Failed to parse binary bitvector: {} ({})", s, e))
    } else {
        Err(format!("Invalid bitvector literal format: {}", s))
    }
}


#[derive_where(Hash, Debug, Clone)]
pub struct Qualifier<T: Types> {
    pub name: String,
    pub args: Vec<(T::Var, Sort<T>)>,
    pub body: Expr<T>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)] // Added Deserialize
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
}

impl FromStr for BinOp {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Plus" => Ok(BinOp::Add), "Minus" => Ok(BinOp::Sub),
            "Times" => Ok(BinOp::Mul), "Div" => Ok(BinOp::Div),
            "Mod" => Ok(BinOp::Mod),
            _ => Err(format!("Unknown BinOp: {}", s)),
        }
    }
}

impl<'de, T: Types> Deserialize<'de> for Constant<T>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field { Tag, Contents }
        struct ConstantVisitor<T: Types>(PhantomData<T>);
        impl<'de, T: Types> Visitor<'de> for ConstantVisitor<T>
        {
            type Value = Constant<T>;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct Constant")
            }
            fn visit_map<V>(self, mut map: V) -> Result<Constant<T>, V::Error>
            where V: MapAccess<'de>,
            {
                let mut tag: Option<String> = None;
                let mut contents_val: Option<serde_json::Value> = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Tag => {
                            if tag.is_some() { return Err(de::Error::duplicate_field("tag")); }
                            tag = Some(map.next_value()?);
                        }
                        Field::Contents => {
                            if contents_val.is_some() { return Err(de::Error::duplicate_field("contents")); }
                            contents_val = Some(map.next_value()?);
                        }
                    }
                }
                let tag = tag.ok_or_else(|| de::Error::missing_field("tag"))?;
                let contents_val = contents_val.ok_or_else(|| de::Error::missing_field("contents"))?;
                match tag.as_str() {
                    "I" => Ok(Constant::Numeral(serde_json::from_value(contents_val).map_err(de::Error::custom)?)),
                    "R" => Ok(Constant::Decimal(serde_json::from_value(contents_val).map_err(de::Error::custom)?)),
                    "L" => {
                        let (text_val, _sort_ignored): (String, serde_json::Value) = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        if text_val == "true" { Ok(Constant::Boolean(true)) }
                        else if text_val == "false" { Ok(Constant::Boolean(false)) }
                        else if text_val.starts_with('"') && text_val.ends_with('"') && text_val.len() >= 2 {
                            let inner_str = text_val[1..text_val.len()-1].to_string();
                            let t_string: T::String = serde_json::from_value(serde_json::Value::String(inner_str))
                                .map_err(|e| de::Error::custom(format_args!("Failed to deserialize to T::String: {}", e)))?;
                            Ok(Constant::String(t_string))
                        } else if text_val.starts_with("#x") || text_val.starts_with("#b") {
                            let (val, size) = parse_bitvec_literal(&text_val).map_err(de::Error::custom)?;
                            Ok(Constant::BitVec(val, size))
                        } else { Err(de::Error::custom(format!("Unknown L-Constant format: {}", text_val))) }
                    }
                    _ => Err(de::Error::unknown_variant(&tag, &["I", "R", "L"])),
                }
            }
        }
        deserializer.deserialize_map(ConstantVisitor(PhantomData))
    }
}

// impl<'de, T: Types> Deserialize<'de> for Sort<T>
// {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where D: Deserializer<'de>,
//     {
//         #[derive(Deserialize)]
//         #[serde(field_identifier, rename_all = "lowercase")]
//         enum Field { Tag, Contents }
//         struct SortVisitor<T: Types>(PhantomData<T>);
//         impl<'de, T: Types> Visitor<'de> for SortVisitor<T>
//         {
//             type Value = Sort<T>;
//             fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result { formatter.write_str("struct Sort") }
//             fn visit_map<V>(self, mut map: V) -> Result<Sort<T>, V::Error>
//             where V: MapAccess<'de>,
//             {
//                 let mut tag: Option<String> = None;
//                 let mut contents_val: Option<serde_json::Value> = None;
//                 while let Some(key) = map.next_key()? {
//                     match key {
//                         Field::Tag => { if tag.is_some() { return Err(de::Error::duplicate_field("tag")); } tag = Some(map.next_value()?); }
//                         Field::Contents => { if contents_val.is_some() { return Err(de::Error::duplicate_field("contents")); } contents_val = Some(map.next_value()?); }
//                     }
//                 }
//                 let tag = tag.ok_or_else(|| de::Error::missing_field("tag"))?;
//                 match tag.as_str() {
//                     "FInt" => Ok(Sort::Int),
//                     "FReal" => Ok(Sort::Real),
//                     "FVar" => Ok(Sort::Var(serde_json::from_value(contents_val.ok_or_else(|| de::Error::missing_field("contents for FVar"))?).map_err(de::Error::custom)?)),
//                     "FFunc" => {
//                         let sorts: [Sort<T>; 2] = serde_json::from_value(contents_val.ok_or_else(|| de::Error::missing_field("contents for FFunc"))?).map_err(de::Error::custom)?;
//                         Ok(Sort::Func(Box::new(sorts)))
//                     }
//                     "FAbs" => {
//                         let (idx, sort_val): (usize, Sort<T>) = serde_json::from_value(contents_val.ok_or_else(|| de::Error::missing_field("contents for FAbs"))?).map_err(de::Error::custom)?;
//                         Ok(Sort::Abs(idx, Box::new(sort_val)))
//                     }
//                     "FTC" => {
//                         let tycon_name: String = serde_json::from_value(contents_val.ok_or_else(|| de::Error::missing_field("contents for FTC"))?).map_err(de::Error::custom)?;
//                         if tycon_name.starts_with("Size") {
//                             if let Some(size_str) = tycon_name.strip_prefix("Size") {
//                                 let size = size_str.parse::<u32>().map_err(|_| de::Error::custom(format!("Invalid BvSize format: {}", tycon_name)))?;
//                                 Ok(Sort::BvSize(size))
//                             } else { Err(de::Error::custom(format!("Invalid BvSize format: {}", tycon_name))) }
//                         } else if tycon_name == "bool" { Ok(Sort::Bool) }
//                         else if tycon_name == "int" { Ok(Sort::Int) } // Map FTC "int" to Sort::Int
//                         else if tycon_name == "real" { Ok(Sort::Real) } // Map FTC "real" to Sort::Real
//                         else if tycon_name == "str" { Ok(Sort::Str) }
//                         else if tycon_name == "Set" { Ok(Sort::App(SortCtor::Set, vec![])) } // Represent bare Set tycon
//                         else if tycon_name == "Map" { Ok(Sort::App(SortCtor::Map, vec![])) } // Represent bare Map tycon
//                         else if tycon_name == "BitVec" {
//                             // This is the FTC for "BitVec" constructor, usually expects an FApp.
//                             // Represent as Sort::App(SortCtor::Data(T::Sort for "BitVec"), [])
//                             let tc_sort: T::Sort = serde_json::from_value(serde_json::Value::String(tycon_name)).map_err(de::Error::custom)?;
//                             Ok(Sort::App(SortCtor::Data(tc_sort), vec![]))
//                         }
//                         else {
//                             let data_sort_name: T::Sort = serde_json::from_value(serde_json::Value::String(tycon_name)).map_err(de::Error::custom)?;
//                             Ok(Sort::App(SortCtor::Data(data_sort_name), vec![]))
//                         }
//                     }
//                     "FApp" => {
//                         let (mut s1, s2): (Sort<T>, Sort<T>) = serde_json::from_value(contents_val.ok_or_else(|| de::Error::missing_field("contents for FApp"))?).map_err(de::Error::custom)?;
//                         // Handle BitVec: FApp (FTC "BitVec") (FTC "SizeN") -> BitVec(BvSize(N))
//                         match s1.clone() {
//                             Sort::App(SortCtor::Data(tc_name), ref args) => {
//                                 if args.is_empty() {
//                                     // Convert T::Sort to a string for comparison if possible, or use a marker.
//                                     // This requires T::Sort to be comparable or convertible to a known string.
//                                     // A more robust way would be to have specific enum variants for known tycons like BitVec.
//                                     // For now, assuming T::Sort can be stringified and compared.
//                                     // This is complex. Let's use a placeholder string name.
//                                     let tc_name_str = format!("{:?}", tc_name); // Simplistic; relies on Debug output
//                                     if tc_name_str.contains("BitVec") { // Check if T::Sort is the BitVec constructor
//                                         if let Sort::BvSize(n) = s2 {
//                                             return Ok(Sort::BitVec(Box::new(Sort::BvSize(n))));
//                                         }
//                                     }
//                                 }
//                             }
//                             // Handle Set: FApp (FTC "Set") ElSort -> App(SortCtor::Set, [ElSort])
//                             Sort::App(SortCtor::Set, ref args) => {
//                             if args.is_empty() { return Ok(Sort::App(SortCtor::Set, vec![s2])); }
//                             }
//                             // Handle Map: FApp (FApp (FTC "Map") KeySort) ValSort -> App(SortCtor::Map, [KeySort, ValSort])
//                             Sort::App(SortCtor::Map, ref args1) => { // s1 is FApp (FTC "Map") KeySort
//                                 if args1.len() == 1 { // args1 contains KeySort
//                                     return Ok(Sort::App(SortCtor::Map, vec![args1[0].clone(), s2]));
//                                 }
//                             }
//                             _ => {}
//                         }
//                         // General FApp: unroll and collect
//                         let mut current = s1.clone();
//                         let mut app_args = vec![s2];
//                         while let Sort::App(f, mut prev_args) = current {
//                              if prev_args.len() == 1 && matches!(f, SortCtor::Data(_)) { // Base case like (FTC "ctor") arg1
//                                 app_args.insert(0, prev_args.remove(0));
//                                 current = Sort::App(f, vec![]); // Represent the base constructor
//                                 break;
//                              } else if prev_args.is_empty() && matches!(f, SortCtor::Data(_) | SortCtor::Set | SortCtor::Map) {
//                                 current = Sort::App(f, vec![]);
//                                 break;
//                              }
//                              // This part is tricky for general FApp unrolling matching Rust's structure.
//                              // The provided example JSON has EApp unrolling, not FApp.
//                              // For now, a simple pass-through which might be incorrect for deeply nested FApps.
//                              return Err(de::Error::custom(format!("General FApp unrolling is complex. Structure: ({:?}, {:?})", current, app_args)));
//                         }
//                         if let Sort::App(ctor, base_args) = current {
//                             if base_args.is_empty() {
//                                 return Ok(Sort::App(ctor, app_args));
//                             }
//                         }
//                         Err(de::Error::custom(format!("Unhandled FApp structure: ({:?}, {:?})", s1, app_args)))
//                     }
//                     _ => Err(de::Error::unknown_variant(&tag, &["FInt", "FReal", "FVar", "FFunc", "FAbs", "FTC", "FApp"])),
//                 }
//             }
//         }
//         deserializer.deserialize_map(SortVisitor(PhantomData))
//     }
// }


impl<'de, T: Types> Deserialize<'de> for Expr<T>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field { Tag, Contents }
        struct ExprVisitor<T: Types>(PhantomData<T>);
        impl<'de, T: Types> Visitor<'de> for ExprVisitor<T>
        {
            type Value = Expr<T>;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result { formatter.write_str("struct Expr") }
            fn visit_map<V>(self, mut map: V) -> Result<Expr<T>, V::Error>
            where V: MapAccess<'de>,
            {
                let mut tag: Option<String> = None;
                let mut contents_val: Option<serde_json::Value> = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Tag => { if tag.is_some() { return Err(de::Error::duplicate_field("tag")); } tag = Some(map.next_value()?); }
                        Field::Contents => { if contents_val.is_some() { return Err(de::Error::duplicate_field("contents")); } contents_val = Some(map.next_value()?); }
                    }
                }
                let tag = tag.ok_or_else(|| de::Error::missing_field("tag"))?;
                let contents_val = contents_val.ok_or_else(|| de::Error::missing_field("contents for a tag"))?;

                match tag.as_str() {
                    "ECon" => Ok(Expr::Constant(serde_json::from_value(contents_val).map_err(de::Error::custom)?)),
                    "EVar" => Ok(Expr::Var(serde_json::from_value(contents_val).map_err(de::Error::custom)?)), "EApp" => {
                        let (mut current_expr, arg): (Expr<T>, Expr<T>) = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        let mut args_vec = vec![arg];
                        while let Expr::App(f, mut prev_args) = current_expr {
                            prev_args.append(&mut args_vec);
                            args_vec = prev_args;
                            current_expr = *f;
                        }
                        Ok(Expr::App(Box::new(current_expr), args_vec))
                    }
                    "ENeg" => Ok(Expr::Neg(Box::new(serde_json::from_value(contents_val).map_err(de::Error::custom)?))),
                    "EBin" => {
                        let (op_str, expr1, expr2): (String, Expr<T>, Expr<T>) = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        let op = BinOp::from_str(&op_str).map_err(de::Error::custom)?;
                        Ok(Expr::BinaryOp(op, Box::new([expr1, expr2])))
                    }
                    "EIte" => Ok(Expr::IfThenElse(Box::new(serde_json::from_value(contents_val).map_err(de::Error::custom)?))),
                    "PAnd" => Ok(Expr::And(serde_json::from_value(contents_val).map_err(de::Error::custom)?)),
                    "POr"  => Ok(Expr::Or(serde_json::from_value(contents_val).map_err(de::Error::custom)?)),
                    "PNot" => Ok(Expr::Not(Box::new(serde_json::from_value(contents_val).map_err(de::Error::custom)?))),
                    "PImp" => {
                        let exprs_arr: [Expr<T>; 2] = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        Ok(Expr::Imp(Box::new(exprs_arr)))
                    }
                    "PIff" => {
                        let exprs_arr: [Expr<T>; 2] = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        Ok(Expr::Iff(Box::new(exprs_arr)))
                    }
                    "PAtom" => {
                        let (rel_str, expr1, expr2): (String, Expr<T>, Expr<T>) = serde_json::from_value(contents_val).map_err(de::Error::custom)?;
                        let rel = BinRel::from_str(&rel_str).map_err(de::Error::custom)?;
                        Ok(Expr::Atom(rel, Box::new([expr1, expr2])))
                    }
                    _ => Err(de::Error::unknown_variant(&tag, &["ECon", "EVar", "EApp", "ENeg", "EBin", "EIte", "PAnd", "POr", "PNot", "PImp", "PIff", "PAtom"])),
                }
            }
        }
        deserializer.deserialize_map(ExprVisitor(PhantomData))
    }
}
