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
    Drop(Local),
    Debug,
}

/// An rvalue appears at the right hand side of an assignment.
#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    Ref(BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}

/// A path to a value
#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<Projection>,
}

impl Place {
    pub fn new<T>(local: Local, projection: T) -> Self
    where
        T: Into<Vec<Projection>>,
    {
        Place {
            local,
            projection: projection.into(),
        }
    }

    pub fn extend<'a, I>(&self, rhs: I) -> Place
    where
        I: IntoIterator<Item = &'a Projection>,
    {
        Place {
            local: self.local,
            projection: self
                .projection
                .iter()
                .copied()
                .chain(rhs.into_iter().copied())
                .collect(),
        }
    }

    pub fn overlaps(&self, rhs: &Place) -> bool {
        if self.local != rhs.local {
            return false;
        }
        for (&p1, &p2) in self.projection.iter().zip(&rhs.projection) {
            if p1 != p2 {
                return false;
            }
        }
        true
    }

    pub fn equals(&self, local: Local, path: &Vec<u32>) -> bool {
        if self.local != local {
            return false;
        }
        for (&proj, &i) in self.projection.iter().zip(path) {
            if let Projection::Field(n) = proj {
                if n != i {
                    return false;
                }
            }
        }
        path.len() == self.projection.len()
    }
}

#[derive(Clone, Debug)]
pub struct Path(pub Vec<u32>);

impl Path {
    pub fn new() -> Self {
        Path(vec![])
    }
}

impl std::ops::Deref for Path {
    type Target = Vec<u32>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Path {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<&Path> for Vec<Projection> {
    fn from(path: &Path) -> Self {
        path.0.iter().copied().map(Projection::from).collect()
    }
}

impl<'a> IntoIterator for &'a Path {
    type Item = &'a u32;

    type IntoIter = std::slice::Iter<'a, u32>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub enum Projection {
    Field(u32),
    Deref,
}

impl From<u32> for Projection {
    fn from(v: u32) -> Self {
        Projection::Field(v)
    }
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

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Constant {
    Bool(bool),
    Int(u128),
    Unit,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum UnOp {
    Not,
}

/// The heap is a mapping between location and types.
pub type Heap<'lr> = Vec<(Location, Ty<'lr>)>;

/// A location into a block of memory in the heap.
#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
pub struct Location(pub Symbol);

/// An environment maps locals to owned references.
pub type Env = Vec<(Local, OwnRef)>;

/// A Local is an identifier to some local variable introduced with a let
/// statement.
#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
pub struct Local(pub Symbol);

/// An owned reference to a location. This is used for arguments and return types.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct OwnRef(pub Location);

impl std::fmt::Display for OwnRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Own({})", self.0)
    }
}

pub type Ty<'lr> = &'lr TyS<'lr>;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct Region(Vec<Place>);

impl Region {
    pub fn new(place: Place) -> Self {
        Self(vec![place])
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn subset_of(&self, rhs: &Region) -> bool {
        for place in &self.0 {
            if rhs.iter().any(|p| place == p) {
                return true;
            }
        }
        false
    }

    pub fn iter(&self) -> impl Iterator<Item = &Place> + '_ {
        self.0.iter()
    }
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .0
            .iter()
            .map(|p| format!("{}", p))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{{ {} }}", s)
    }
}

impl<'a> IntoIterator for &'a Region {
    type Item = &'a Place;

    type IntoIter = std::slice::Iter<'a, Place>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl From<Vec<Place>> for Region {
    fn from(v: Vec<Place>) -> Self {
        Self(v)
    }
}

impl std::ops::Index<usize> for Region {
    type Output = Place;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug, PartialOrd)]
pub enum BorrowKind {
    Shared,
    Mut,
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BorrowKind::Shared => write!(f, "shared"),
            BorrowKind::Mut => write!(f, "mutable"),
        }
    }
}

impl BorrowKind {
    pub fn is_mut(&self) -> bool {
        match self {
            BorrowKind::Shared => false,
            BorrowKind::Mut => true,
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug)]
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
    /// A mutable reference
    Ref(BorrowKind, Region, Location),
    /// A refinement type { bind: ty | pred }.
    Refine { ty: BasicType, pred: Pred<'lr> },
    /// A dependent tuple.
    Tuple(Vec<(Field, &'lr TyS<'lr>)>),
    /// Unitialized
    Uninit(u32),
    /// A refinement that need to be inferred
    RefineHole { ty: BasicType },
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

impl std::fmt::Display for BasicType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BasicType::Bool => write!(f, "bool"),
            BasicType::Int => write!(f, "int"),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Field(pub Symbol);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Var {
    Nu,
    Location(Location),
    Field(Field),
}

pub type Pred<'lr> = &'lr PredS<'lr>;

#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
pub enum ConstantP {
    Bool(bool),
    Int(u128),
}

/// A refinement type predicate
#[derive(Eq, PartialEq, Hash, Debug)]
pub enum PredS<'lr> {
    Constant(ConstantP),
    Place { var: Var, projection: Vec<u32> },
    BinaryOp(BinOp, &'lr PredS<'lr>, &'lr PredS<'lr>),
    UnaryOp(UnOp, &'lr PredS<'lr>),
    Iff(&'lr PredS<'lr>, &'lr PredS<'lr>),
    Kvar(u32, Vec<Var>),
}

impl<'lr> TyS<'lr> {
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            TyS::Refine {
                ty: BasicType::Int,
                ..
            }
        )
    }

    pub fn is_copy(&self) -> bool {
        match self {
            TyS::Refine { .. } => true,
            TyS::Tuple(fields) => fields.iter().all(|(_, t)| t.is_copy()),
            TyS::Ref(BorrowKind::Shared, ..) => true,
            _ => false,
        }
    }

    pub fn size(&self) -> u32 {
        match self {
            TyS::Fn { .. } | TyS::OwnRef(_) | TyS::Ref(..) => 1,
            TyS::Refine { .. } | TyS::RefineHole { .. } => 1,
            TyS::Tuple(fields) => fields.iter().map(|f| f.1.size()).sum(),
            TyS::Uninit(size) => *size,
        }
    }

    pub fn walk(&'lr self, mut act: impl FnMut(&Path, Ty<'lr>)) {
        self.walk_(
            &mut |path, typ| Ok::<(), ()>(act(path, typ)),
            &mut Path::new(),
        )
        .unwrap()
    }

    pub fn try_walk<T>(
        &'lr self,
        mut act: impl FnMut(&Path, Ty<'lr>) -> Result<(), T>,
    ) -> Result<(), T> {
        self.walk_(&mut act, &mut Path::new())
    }

    fn walk_<T>(
        &'lr self,
        act: &mut impl FnMut(&Path, Ty<'lr>) -> Result<(), T>,
        path: &mut Path,
    ) -> Result<(), T> {
        act(path, self)?;
        match self {
            TyS::Tuple(fields) => {
                for i in 0..fields.len() {
                    path.push(i as u32);
                    fields[i].1.walk_(act, path)?;
                    path.pop();
                }
            }
            _ => {}
        }
        Ok(())
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

impl<'a> Into<TyS<'a>> for OwnRef {
    fn into(self) -> TyS<'a> {
        TyS::OwnRef(self.0)
    }
}

// -------------------------------------------------------------------------------------------------
// DEBUG
// -------------------------------------------------------------------------------------------------

impl std::fmt::Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &*self.0.as_str())
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &*self.0.as_str())
    }
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Int(i) => write!(f, "{}", i),
            Constant::Unit => write!(f, "()"),
        }
    }
}

impl std::fmt::Display for ConstantP {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantP::Bool(b) => write!(f, "{}", b),
            ConstantP::Int(i) => write!(f, "{}", i),
        }
    }
}

impl std::fmt::Display for BinOp {
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

impl std::fmt::Display for PredS<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredS::Constant(c) => write!(f, "{}", c)?,
            PredS::Place { var, projection } => {
                write!(f, "{}", var)?;
                for p in projection {
                    write!(f, ".{}", p)?
                }
            }
            PredS::BinaryOp(op, lhs, rhs) => {
                write!(f, "({} {} {})", lhs, op, rhs)?;
            }
            PredS::UnaryOp(op, operand) => {
                write!(f, "{}({})", op, operand)?;
            }
            PredS::Iff(rhs, lhs) => {
                write!(f, "({} <=> {})", rhs, lhs)?;
            }
            PredS::Kvar(n, vars) => {
                let vars = vars
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "$k{}[{}]", n, vars)?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Display for TyS<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyS::Fn { .. } => write!(f, "function"),
            TyS::OwnRef(l) => write!(f, "Own({})", l),
            TyS::Refine { ty, pred } => write!(f, "{{ {} | {} }}", ty, pred),
            TyS::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|(x, t)| format!("@{}: {}", x, t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", fields)
            }
            TyS::Uninit(size) => write!(f, "Uninit({})", size),
            TyS::RefineHole { ty, .. } => write!(f, "{{ {} | _ }}", ty),
            TyS::Ref(BorrowKind::Mut, r, l) => write!(f, "&mut({}, {})", r, l),
            TyS::Ref(BorrowKind::Shared, r, l) => write!(f, "&({}, {})", r, l),
        }
    }
}

impl std::fmt::Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Nu => write!(f, "_v"),
            Var::Location(s) => write!(f, "l${}", *&s.0),
            Var::Field(s) => write!(f, "f${}", *&s.0),
        }
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "¬"),
        }
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("{}", self.local);
        let mut needs_parens = false;
        for p in &self.projection {
            match p {
                Projection::Field(n) => {
                    if needs_parens {
                        s = format!("({}).{}", s, n);
                        needs_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                Projection::Deref => {
                    s = format!("*{}", s);
                    needs_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }
}
