#![feature(rustc_private)]

use liquid_rust_common::index::Index;
use liquid_rust_mir::{BBlockId, FuncId, Span};
use liquid_rust_ty::{BaseTy, BinOp, LocalVariable, Predicate, UnOp, Variable};

use std::{
    collections::BTreeMap,
    io::{self, Write},
};

/// An environment binding of a variable to a base type and a predicate.
struct Bind {
    variable: LocalVariable,
    base_ty: BaseTy,
    predicate: Predicate,
}

/// An environment constraint that must hold for the program to be well-typed.
///
/// All constraints have the form `b : base_ty . lhs  => rhs`.
struct Constraint {
    /// The environment for this constraint.
    ///
    /// Each variable here must have a valid binding inside the `Emitter.env` field.
    env: Vec<LocalVariable>,
    /// The base type of the variable bound by the constraint.
    base_ty: BaseTy,
    /// The left-hand side of the implication.
    lhs: Predicate,
    /// The right-hand side of the implication.
    rhs: Predicate,
    /// The span where an error should be reported if this constraint is false.
    span: Span,
}

/// A struct used to emit constraints.
pub struct Emitter {
    /// All the environment bindings.
    env: Vec<Bind>,
    /// All the constraints for the current program.
    constraints: Vec<Constraint>,
    bb_id: Option<BBlockId>,
    func_id: FuncId,
}

impl Emitter {
    /// Create a new empty emitter
    pub fn new(func_id: FuncId) -> Self {
        Self {
            env: Vec::new(),
            constraints: Vec::new(),
            bb_id: None,
            func_id,
        }
    }

    pub fn set_bb(&mut self, bb_id: BBlockId) {
        self.bb_id = Some(bb_id);
    }

    pub fn unset_bb(&mut self) {
        self.bb_id = None;
    }

    pub fn set_func(&mut self, func_id: FuncId) {
        self.func_id = func_id;
    }

    /// Add a binding in the current environment.
    pub fn add_bind(&mut self, variable: LocalVariable, base_ty: BaseTy, predicate: Predicate) {
        self.env.push(Bind {
            variable,
            base_ty,
            predicate,
        });
    }

    /// Add a constraint to be emitted later.
    pub fn add_constraint(
        &mut self,
        env: Vec<LocalVariable>,
        base_ty: BaseTy,
        lhs: Predicate,
        rhs: Predicate,
        span: Span,
    ) {
        self.constraints.push(Constraint {
            env,
            base_ty,
            lhs,
            rhs,
            span,
        });
    }
}

impl Emitter {
    /// Emit all the constraints into a file.
    pub fn emit(self) -> io::Result<()> {
        let mut file = std::fs::File::create("./output.fq")?;
        // The index of the binding for each variable.
        let mut vars = BTreeMap::new();

        // First we emit all the environment bindings.
        for (index, bind) in self.env.iter().enumerate() {
            // Store the index for the variable.
            vars.insert(bind.variable, index);

            // Bindings are emitted with this format:
            // `bind <index> : { <variable> : <base_ty> | <predicate>}`.
            write!(file, "bind {} ", index)?;
            bind.variable.emit(&mut file, &self)?;
            write!(file, " : {{")?;
            Variable::Bound.emit(&mut file, &self)?;
            write!(file, ": ")?;
            bind.base_ty.emit(&mut file, &self)?;
            write!(file, " | ")?;
            bind.predicate.emit(&mut file, &self)?;
            writeln!(file, "}}")?;
        }

        for (id, constraint) in self.constraints.iter().enumerate() {
            println!(
                "Emitting constraint {} with span {:?}.",
                id, constraint.span
            );

            writeln!(file, "\nconstraint:")?;

            // The `env` field  has the format `env [<index> ; ...]` where `index` ranges over the
            // indices of the binding for each variable in the environment of the constraint.
            write!(file, "\tenv [")?;
            let mut env = constraint.env.iter();
            if let Some(var) = env.next() {
                write!(file, "{}", vars[&var])?;
                for var in env {
                    write!(file, "; {}", vars[&var])?;
                }
            }
            writeln!(file, "]")?;

            // The `lhs` field has the format `lhs { b : <base_ty> | <lhs> }`.
            write!(file, "\tlhs {{")?;
            Variable::Bound.emit(&mut file, &self)?;
            write!(file, ": ")?;
            constraint.base_ty.emit(&mut file, &self)?;
            write!(file, " | ")?;
            constraint.lhs.emit(&mut file, &self)?;
            writeln!(file, "}}")?;

            // The `lhs` field has the format `rhs { b : <base_ty> | <lhs> }`.
            write!(file, "\trhs {{")?;
            Variable::Bound.emit(&mut file, &self)?;
            write!(file, ": ")?;
            constraint.base_ty.emit(&mut file, &self)?;
            write!(file, " | ")?;
            constraint.rhs.emit(&mut file, &self)?;
            writeln!(file, "}}")?;

            // The `id` field has the format `id <id> tag []`.
            //
            // This `<id>` can be used to display error information.
            writeln!(file, "\tid {} tag []", id)?;
        }

        Ok(())
    }
}

/// The trait that every type that can be emitted by `Emitter` must implement.
trait Emit {
    /// Emit a value into a buffer.
    fn emit<W: Write>(&self, writer: &mut W, emitter: &Emitter) -> io::Result<()>;
}

impl Emit for LocalVariable {
    fn emit<W: Write>(&self, writer: &mut W, emitter: &Emitter) -> io::Result<()> {
        match emitter.bb_id {
            Some(bb_id) => write!(writer, "{}_{}_{}", self, bb_id, emitter.func_id),
            None => write!(writer, "{}_init_{}", self, emitter.func_id),
        }
    }
}

impl Emit for Variable {
    fn emit<W: Write>(&self, writer: &mut W, emitter: &Emitter) -> io::Result<()> {
        match self {
            Variable::Bound => write!(writer, "b"),
            Variable::Local(a) => a.emit(writer, emitter),
            // All arguments should have been projected.
            Variable::Arg(_) => unreachable!(),
        }
    }
}

impl Emit for Predicate {
    fn emit<W: Write>(&self, writer: &mut W, emitter: &Emitter) -> io::Result<()> {
        match self {
            // Literals are emitted in the same way as they are displayed.
            Predicate::Lit(literal) => write!(writer, "{}", literal),
            // Literals are emitted according to their `Emit` implementation.
            Predicate::Var(variable) => variable.emit(writer, emitter),
            // Unary operations are emitted between parentheses.
            Predicate::UnaryOp(un_op, op) => {
                write!(writer, "(")?;
                un_op.emit(writer, emitter)?;
                write!(writer, " ")?;
                op.emit(writer, emitter)?;
                write!(writer, ")")
            }
            // Binary operations are emitted between parentheses.
            Predicate::BinaryOp(bin_op, op1, op2) => {
                write!(writer, "(")?;
                op1.emit(writer, emitter)?;
                write!(writer, " ")?;
                bin_op.emit(writer, emitter)?;
                write!(writer, " ")?;
                op2.emit(writer, emitter)?;
                write!(writer, ")")
            }
            // Inference variables are emitted using its index.
            Predicate::Hole(hole) => write!(writer, "p{}", hole.id.index()),
        }
    }
}

impl<A: Emit> Emit for &A {
    fn emit<W: Write>(&self, writer: &mut W, emitter: &Emitter) -> io::Result<()> {
        (*self).emit(writer, emitter)
    }
}

impl Emit for UnOp {
    fn emit<W: Write>(&self, writer: &mut W, _emitter: &Emitter) -> io::Result<()> {
        match self {
            // Use `not` instead of `!`.
            UnOp::Not { .. } => write!(writer, "not"),
            _ => write!(writer, "{}", self),
        }
    }
}

impl Emit for BinOp {
    fn emit<W: Write>(&self, writer: &mut W, _emitter: &Emitter) -> io::Result<()> {
        match self {
            // Use `<=>` instead of `==` for booleans.
            BinOp::Eq(BaseTy::Bool) => write!(writer, "<=>"),
            _ => write!(writer, "{}", self),
        }
    }
}

impl Emit for BaseTy {
    fn emit<W: Write>(&self, writer: &mut W, _emitter: &Emitter) -> io::Result<()> {
        let s = match self {
            BaseTy::Unit => "unit",
            BaseTy::Bool => "bool",
            // Emit all integer types as `int`.
            BaseTy::Int { .. } => "int",
        };

        write!(writer, "{}", s)
    }
}
