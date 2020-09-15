use rustc_span::Symbol;

/// A function definition
#[derive(Debug)]
pub struct FnDef<'lr> {
    /// Name of the function.
    pub name: Symbol,
    /// The input heap.
    pub heap: Heap<'lr>,
    /// Formal arguments of the function. These are always owned references so we
    /// represent them directly as locations in the input heap.
    pub args: Vec<(Local, Location)>,
    /// The return continuation.
    pub ret: Symbol,
    /// The output heap. This is right now only used to add refinements for the returned
    /// reference but it should be extended to capture the state of the output heap.
    pub out_heap: Heap<'lr>,
    /// Location in the output heap of the returned owned reference.
    pub ret_loc: Location,
    /// Body of the function.
    pub body: Box<FnBody<'lr>>,
}

/// Function body in cps.
#[derive(Debug)]
pub enum FnBody<'lr> {
    /// A continuation definition.
    LetCont {
        /// Name of the continuation.
        name: Symbol,
        /// Heap required to call the continuation.
        heap: Heap<'lr>,
        /// Environment required to call the continuation.
        env: Env,
        /// Additional parameters for the continuation.
        params: Vec<(Local, Location)>,
        /// The body of the continuation.
        body: Box<FnBody<'lr>>,
        /// The rest of the function body.
        rest: Box<FnBody<'lr>>,
    },

    /// Evaluates either the then or else branch depending on the value of the discriminant
    Ite {
        /// The discriminant value being tested.
        discr: Place,
        /// The branch to execute if the discriminant is true.
        then_branch: Box<FnBody<'lr>>,
        /// The branch to execute if the discriminant is false.
        else_branch: Box<FnBody<'lr>>,
    },

    /// Function call
    Call {
        /// Name of the function to be called.
        func: Symbol,
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
}

/// A path to a value
#[derive(Debug)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<u32>,
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

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Constant {
    Bool(bool),
    Int(u128),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

/// The heap is a mapping between location and types.
pub type Heap<'lr> = Vec<(Location, Ty<'lr>)>;

/// A location into a block of memory in the heap.
#[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
pub struct Location(pub Symbol);

/// An environment maps locals to types.
/// These are restricted to reference types.
pub type Env = Vec<(Local, RefType)>;

/// A Local is an identifier to some local variable introduced with a let
/// statement.
#[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
pub struct Local(pub Symbol);

/// A reference type. For now this only contains owned references
/// but it should be extended with shared and mutable references.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum RefType {
    Own(Location),
}

pub type Ty<'lr> = &'lr TyS<'lr>;

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum TyS<'lr> {
    /// A function type
    Fn {
        /// The input heap.
        in_heap: Heap<'lr>,
        /// Formal arguments of the function. These are always owned references so we
        /// represent them directly as locations in the input heap.
        args: Vec<Location>,
        /// The output heap. This is right now only used to add a refinement for the returned
        /// reference but it should be extended to capture the state of the output heap.
        out_heap: Heap<'lr>,
        /// Location in the output heap of the returned owned reference.
        ret_loc: Location,
    },
    /// A reference type
    Ref(RefType),
    /// A refinement type { bind: ty | pred }
    Refine {
        bind: Var,
        ty: BasicType,
        pred: Pred<'lr>,
    },
    /// A dependent tuple.
    Tuple(Vec<(Var, &'lr TyS<'lr>)>),
    /// Unitialized
    Uninit(u32),
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

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Var(pub Symbol);

pub type Pred<'lr> = &'lr PredS<'lr>;

/// A refinement type predicate
#[derive(Debug, Eq, PartialEq, Hash)]
pub enum PredS<'lr> {
    Constant(Constant),
    Place { var: Var, projection: Vec<u32> },
    BinaryOp(BinOp, &'lr PredS<'lr>, &'lr PredS<'lr>),
}

impl Var {
    pub fn intern(string: &str) -> Var {
        Var(Symbol::intern(string))
    }
}
