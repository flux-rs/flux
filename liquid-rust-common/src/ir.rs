use crate::{
    def_index,
    index::{Index, IndexMap, IndexMapBuilder},
    ty::{Argument, BaseTy, IntSize, Predicate, Ty, Variable},
};

use std::fmt;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Literal {
    Unit,
    Bool(bool),
    Uint(u128, IntSize),
    Int(i128, IntSize),
}

impl Literal {
    pub fn as_singleton<A>(&self) -> Ty<A> {
        let base_ty = match self {
            Self::Unit => BaseTy::Unit,
            Self::Bool(_) => BaseTy::Bool,
            Self::Uint(_, size) => BaseTy::Uint(*size),
            Self::Int(_, size) => BaseTy::Int(*size),
        };

        Ty::Refined(
            base_ty,
            Predicate::BinApp(
                BinOp::Eq,
                Box::new(Predicate::Var(Variable::Bounded)),
                Box::new(Predicate::Lit(*self)),
            ),
        )
    }
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<()> for Literal {
    fn from((): ()) -> Self {
        Self::Unit
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool(b) => b.fmt(f),
            Self::Uint(uint, _) => uint.fmt(f),
            Self::Int(int, _) => int.fmt(f),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Lte => "<=",
            Self::Gte => ">=",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };

        s.fmt(f)
    }
}

def_index!(Local);

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

pub enum Operand {
    Local(Local),
    Literal(Literal),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(local) => local.fmt(f),
            Self::Literal(literal) => literal.fmt(f),
        }
    }
}

pub enum Rvalue {
    Use(Operand),
    UnApp(UnOp, Operand),
    BinApp(BinOp, Operand, Operand),
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Use(operand) => operand.fmt(f),
            Self::UnApp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinApp(bin_op, op1, op2) => write!(f, "{} {} {}", op1, bin_op, op2),
        }
    }
}

pub enum Statement {
    Noop,
    Assign(Local, Rvalue),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Noop => "noop".fmt(f),
            Self::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}

pub enum Terminator {
    Return,
    Goto(BBlockId),
    Assert(Operand, bool, BBlockId),
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Return => "return".fmt(f),
            Self::Goto(bb_id) => write!(f, "goto {}", bb_id),
            Self::Assert(op, true, bb_id) => write!(f, "assert({}) -> {}", op, bb_id),
            Self::Assert(op, false, bb_id) => write!(f, "assert(!{}) -> {}", op, bb_id),
        }
    }
}

def_index!(BBlockId);

impl fmt::Display for BBlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

pub struct BBlock {
    statements: Box<[Statement]>,
    terminator: Terminator,
}

impl BBlock {
    pub fn statements(&self) -> &[Statement] {
        self.statements.as_ref()
    }

    pub fn terminator(&self) -> &Terminator {
        &self.terminator
    }
}

impl BBlock {
    pub fn builder() -> BBlockBuilder {
        BBlockBuilder {
            statements: Vec::new(),
            terminator: None,
        }
    }
}

pub struct BBlockBuilder {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

impl BBlockBuilder {
    pub fn add_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn add_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    pub fn build(self) -> Option<BBlock> {
        Some(BBlock {
            statements: self.statements.into_boxed_slice(),
            terminator: self.terminator?,
        })
    }
}

pub struct Func {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMap<BBlockId, BBlock>,
    ty: Ty,
    user_ty: bool,
}

impl Func {
    pub fn builder(arity: usize, bblocks_len: usize) -> FuncBuilder {
        FuncBuilder {
            arity,
            local_decls: Local::index_map(),
            bblocks: BBlockId::index_map_builder(bblocks_len),
            ty: None,
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn return_ty(&self) -> &BaseTy {
        self.local_decls.get(Local::first())
    }

    pub fn arguments(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls.iter().skip(1).take(self.arity)
    }

    pub fn temporaries(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls.iter().skip(self.arity + 1)
    }

    pub fn get_bblock(&self, bblock_id: BBlockId) -> &BBlock {
        self.bblocks.get(bblock_id)
    }

    pub fn ty(&self) -> &Ty {
        &self.ty
    }

    pub fn user_ty(&self) -> bool {
        self.user_ty
    }
}

pub struct FuncBuilder {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMapBuilder<BBlockId, BBlock>,
    ty: Option<Ty>,
}

impl FuncBuilder {
    pub fn bblock_ids(&self) -> impl Iterator<Item = BBlockId> {
        self.bblocks.keys()
    }

    pub fn add_local_decl(&mut self, ty: BaseTy) -> Local {
        self.local_decls.insert(ty)
    }

    pub fn set_bblock(&mut self, bblock_id: BBlockId, bblock: BBlock) -> bool {
        self.bblocks.insert(bblock_id, bblock)
    }

    pub fn add_ty(&mut self, ty: Ty) {
        self.ty = Some(ty);
    }

    pub fn build(self) -> Result<Func, BBlockId> {
        let bblocks = self.bblocks.build()?;
        let (ty, user_ty) = if let Some(ty) = self.ty {
            (ty, true)
        } else {
            let arguments = self
                .local_decls
                .iter()
                .skip(1)
                .take(self.arity)
                .enumerate()
                .map(|(pos, (_, base_ty))| (Argument::new(pos, 0), base_ty.refined()))
                .collect::<Vec<_>>();

            let return_ty = self.local_decls.get(Local::first()).refined();

            (Ty::Func(arguments, Box::new(return_ty)), false)
        };
        Ok(Func {
            arity: self.arity,
            local_decls: self.local_decls,
            bblocks,
            ty,
            user_ty,
        })
    }
}

def_index!(FuncId);

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func{}", self.0)
    }
}

pub struct Program {
    functions: IndexMap<FuncId, Func>,
}

impl Program {
    pub fn builder(functions_len: usize) -> ProgramBuilder {
        ProgramBuilder {
            functions: FuncId::index_map_builder(functions_len),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (FuncId, &Func)> {
        self.functions.iter()
    }

    pub fn get_func(&self, func_id: FuncId) -> &Func {
        self.functions.get(func_id)
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (func_id, func) in self.iter() {
            write!(f, "\n{}", func_id)?;

            if func.user_ty() {
                write!(f, ": {}", func.ty())?;
            }

            write!(f, " = fn(")?;

            let mut arguments = func.arguments();

            if let Some((argument, ty)) = arguments.next() {
                write!(f, "{}: {}", argument, ty)?;

                for (argument, ty) in arguments {
                    write!(f, ", {}: {}", argument, ty)?;
                }
            }

            writeln!(f, ") -> {} {{", func.return_ty())?;

            for (local, ty) in func.temporaries() {
                writeln!(f, "\t{}: {};", local, ty)?;
            }

            for (bb_id, bb) in func.bblocks.iter() {
                writeln!(f, "\n\t{}: {{", bb_id)?;

                for statement in bb.statements() {
                    if !matches!(statement, Statement::Noop) {
                        writeln!(f, "\t\t{};", statement)?;
                    }
                }

                writeln!(f, "\t\t{};", bb.terminator())?;

                writeln!(f, "\t}}")?;
            }

            writeln!(f, "}}")?;
        }

        Ok(())
    }
}

pub struct ProgramBuilder {
    functions: IndexMapBuilder<FuncId, Func>,
}

impl ProgramBuilder {
    pub fn add_func(&mut self, func_id: FuncId, func: Func) -> bool {
        self.functions.insert(func_id, func)
    }

    pub fn func_ids(&self) -> impl Iterator<Item = FuncId> {
        self.functions.keys()
    }

    pub fn build(self) -> Result<Program, FuncId> {
        Ok(Program {
            functions: self.functions.build()?,
        })
    }
}
