use std::fmt::Debug;

pub use rustc_span::Symbol;

/// A function definition
#[derive(Debug)]
pub struct FnDef<'lr> {
    /// Name of the function.
    pub name: Symbol,
    /// The input heap.
    pub heap: Heap<'lr>,
    /// Formal arguments of the function. These are always owned references.
    pub args: Vec<(Local, OwnRef)>,
    /// The return continuation.
    pub ret: Symbol,
    /// The output heap. This is right now only used to add refinements for the returned
    /// reference but it should be extended to capture the state of the output heap.
    pub out_heap: Heap<'lr>,
    /// Returned owned reference.
    pub out_ty: OwnRef,
    /// Body of the function.
    pub body: Box<FnBody<'lr>>,
}

#[derive(Debug)]
pub struct ContDef<'lr> {
    /// Name of the continuation.
    pub name: Symbol,
    /// Heap required to call the continuation.
    pub heap: Heap<'lr>,
    /// Environment required to call the continuation.
    pub env: Env,
    /// Additional parameters for the continuation.
    pub params: Vec<(Local, OwnRef)>,
    /// The body of the continuation.
    pub body: Box<FnBody<'lr>>,
}

/// Function body in cps.
#[derive(Debug)]
pub enum FnBody<'lr> {
    /// A continuation definition.
    LetCont {
        /// Continuation definition.
        def: ContDef<'lr>,
        /// The rest of the function body.
        rest: Box<FnBody<'lr>>,
    },

    /// Evaluates either the then or else branch depending on the value of the discriminant
    Ite {
        /// The discriminant value being tested.
        discr: Place,
        /// The branch to execute if the discriminant is true.
        then: Box<FnBody<'lr>>,
        /// The branch to execute if the discriminant is false.
        else_: Box<FnBody<'lr>>,
    },

    /// Function call
    Call {
        /// Name of the function to be called.
        func: Place,
        /// Arguments the function is called with. These are owned by the callee, which is free
        /// to modify them, i.e., arguments are always moved.
        args: Vec<Local>,
        /// The return continuation.
        ret: Symbol,
    },

    /// Jump to a continuation
    Jump {
        /// The target continuation.
        target: Symbol,
        /// Additional arguments to call the continuation with.
        args: Vec<Local>,
    },

    /// Sequencing of a statement and the rest of the function body
    Seq(Statement, Box<FnBody<'lr>>),

    /// Aborts the execution of the program
    Abort,
}

/// An statement
#[derive(Debug)]
pub enum Statement {
    /// Allocates a block of memory and binds the result to a local.
    /// The type layout is needed for the type system to know the recursive structure
    /// of the type a priori.
    Let(Local, TypeLayout),
    /// Either moves or copies the rvalue to a place.
    Assign(Place, Rvalue),
}

/// An rvalue appears at the right hand side of an assignment.
#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}

/// A path to a value
#[derive(Debug)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<u32>,
}

impl From<Local> for Place {
    fn from(local: Local) -> Self {
        Place {
            local,
            projection: vec![],
        }
    }
}

/// These are values that can appear inside an rvalue. They are intentionally limited to prevent
/// rvalues from being nested in one another.
#[derive(Debug)]
pub enum Operand {
    /// A place dereference *p. This may move or copy depending on the type of p.
    Deref(Place),
    /// A constant value
    Constant(Constant),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Constant {
    Bool(bool),
    Int(u128),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum UnOp {
    Not,
}

/// The heap is a mapping between location and types.
pub type Heap<'lr> = Vec<(Location, Ty<'lr>)>;

/// A location into a block of memory in the heap.
#[derive(Eq, PartialEq, Hash, Copy, Clone)]
pub struct Location(pub Symbol);

/// An environment maps locals to owned references.
pub type Env = Vec<(Local, OwnRef)>;

/// A Local is an identifier to some local variable introduced with a let
/// statement.
#[derive(Eq, PartialEq, Hash, Copy, Clone)]
pub struct Local(pub Symbol);

/// An owned reference to a location. This is used for arguments and return types.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct OwnRef(pub Location);

pub type Ty<'lr> = &'lr TyS<'lr>;

#[derive(Eq, PartialEq, Hash)]
pub enum TyS<'lr> {
    /// A function type
    Fn {
        /// The input heap.
        in_heap: Heap<'lr>,
        /// Formal arguments of the function. These are always owned references so we
        /// represent them directly as locations in the input heap.
        params: Vec<OwnRef>,
        /// The output heap. This is right now only used to add a refinement for the returned
        /// reference but it should be extended to capture the state of the output heap.
        out_heap: Heap<'lr>,
        /// Location in the output heap of the returned owned reference.
        ret: OwnRef,
    },
    /// An owned reference
    OwnRef(Location),
    /// A refinement type { bind: ty | pred }.
    Refine { ty: BasicType, pred: Pred<'lr> },
    /// A dependent tuple.
    Tuple(Vec<(Field, &'lr TyS<'lr>)>),
    /// Unitialized
    Uninit(u32),
    /// A refinment that need to be inferred
    RefineHole { ty: BasicType, n: u32 },
}

/// A type layout is used to describe the recursive structure of a type.
#[derive(Debug)]
pub enum TypeLayout {
    /// Tuples decompose memory recursively.
    Tuple(Vec<TypeLayout>),
    /// A block of memory that cannot be further decomposed recursively.
    Block(u32),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum BasicType {
    Bool,
    Int,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Field(pub Symbol);

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Var {
    Nu,
    Location(Location),
    Field(Field),
}

pub type Pred<'lr> = &'lr PredS<'lr>;

/// A refinement type predicate
#[derive(Eq, PartialEq, Hash)]
pub enum PredS<'lr> {
    Constant(Constant),
    Place { var: Var, projection: Vec<u32> },
    BinaryOp(BinOp, &'lr PredS<'lr>, &'lr PredS<'lr>),
    UnaryOp(UnOp, &'lr PredS<'lr>),
    Iff(&'lr PredS<'lr>, &'lr PredS<'lr>),
    Kvar(u32, Vec<Var>),
}

impl<'lr> TyS<'lr> {
    pub fn is_int(&self) -> bool {
        matches!(self, TyS::Refine { ty: BasicType::Int, .. })
    }

    pub fn project(&'lr self, proj: &[u32]) -> Ty<'lr> {
        match (self, proj) {
            (_, []) => self,
            (TyS::Tuple(fields), [n, ..]) => fields[*n as usize].1.project(&proj[1..]),
            _ => bug!("Wrong projection: `{:?}.{:?}`", self, proj),
        }
    }

    pub fn is_copy(&self) -> bool {
        // TODO
        true
    }

    pub fn size(&self) -> u32 {
        match self {
            TyS::Fn { .. } => 1,
            TyS::OwnRef(_) => 1,
            TyS::Refine { .. } | TyS::RefineHole { .. } => 1,
            TyS::Tuple(fields) => fields.iter().map(|f| f.1.size()).sum(),
            TyS::Uninit(size) => *size,
        }
    }
}

impl Field {
    pub fn intern(string: &str) -> Self {
        Self(Symbol::intern(string))
    }

    pub fn nth(n: u32) -> Self {
        Self::intern(&format!("{}", n))
    }
}

impl From<Location> for Var {
    fn from(v: Location) -> Self {
        Var::Location(v)
    }
}

impl From<Field> for Var {
    fn from(f: Field) -> Self {
        Var::Field(f)
    }
}

impl Constant {
    pub fn ty(&self) -> BasicType {
        match self {
            Constant::Bool(_) => BasicType::Bool,
            Constant::Int(_) => BasicType::Int,
        }
    }
}

impl<'a> Into<TyS<'a>> for OwnRef {
    fn into(self) -> TyS<'a> {
        TyS::OwnRef(self.0)
    }
}

// -------------------------------------------------------------------------------------------------
// DEBUG
// -------------------------------------------------------------------------------------------------

impl Debug for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Debug for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Debug for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Int(i) => write!(f, "{}", i),
        }
    }
}

impl Debug for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Eq => write!(f, "="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Gt => write!(f, ">"),
        }
    }
}

impl Debug for PredS<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredS::Constant(c) => Debug::fmt(&c, f)?,
            PredS::Place { var, projection } => {
                write!(f, "{:?}", var)?;
                for p in projection {
                    write!(f, ".{}", p)?
                }
            }
            PredS::BinaryOp(op, lhs, rhs) => {
                write!(f, "({:?} {:?} {:?})", lhs, op, rhs)?;
            }
            PredS::UnaryOp(op, operand) => {
                write!(f, "{:?}({:?})", op, operand)?;
            }
            PredS::Iff(rhs, lhs) => {
                write!(f, "({:?} <=> {:?})", rhs, lhs)?;
            }
            PredS::Kvar(n, vars) => {
                write!(f, "$k{}{:?}", n, vars)?;
            }
        }
        Ok(())
    }
}

impl Debug for TyS<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyS::Fn { .. } => write!(f, "function"),
            TyS::OwnRef(l) => write!(f, "OwnRef({:?})", l),
            TyS::Refine { ty, pred } => write!(f, "{{ {:?} | {:?} }}", ty, pred),
            TyS::Tuple(fields) => write!(f, "{:?}", fields),
            TyS::Uninit(size) => write!(f, "Uninit({})", size),
            TyS::RefineHole { ty, .. } => write!(f, "{{ {:?} | _ }}", ty),
        }
    }
}

impl Debug for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Nu => write!(f, "_v"),
            Var::Location(s) => write!(f, "l${}", *&s.0),
            Var::Field(s) => write!(f, "f${}", *&s.0),
        }
    }
}

impl Debug for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "¬"),
        }
    }
}
