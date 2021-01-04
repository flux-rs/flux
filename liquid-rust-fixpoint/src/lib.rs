use liquid_rust_ty::{BaseTy, BinOp, Predicate, UnOp, Variable};
use liquid_rust_common::index::Index;

use std::{
    collections::BTreeMap,
    io::{self, Write},
};

/// An environment binding of a variable to a base type and a predicate.
struct Bind<A> {
    variable: A,
    base_ty: BaseTy,
    predicate: Predicate<A>,
}

/// An environment constraint that must hold for the program to be well-typed.
///
/// All constraints have the form `b : base_ty . lhs  => rhs`.
struct Constraint<A, S> {
    /// The environment for this constraint.
    ///
    /// Each variable here must have a valid binding inside the `Emitter.env` field.
    env: Vec<A>,
    /// The base type of the variable bound by the constraint.
    base_ty: BaseTy,
    /// The left-hand side of the implication.
    lhs: Predicate<A>,
    /// The right-hand side of the implication.
    rhs: Predicate<A>,
    /// The span where an error should be reported if this constraint is false.
    span: S,
}

/// A struct used to emit constraints.
pub struct Emitter<A, S> {
    /// All the environment bindings.
    env: Vec<Bind<A>>,
    /// All the constraints for the current program.
    constraints: Vec<Constraint<A, S>>,
}

impl<A: Emit + Copy + Ord, S> Emitter<A, S> {
    /// Create a new empty emitter
    pub fn new() -> Self {
        Self {
            env: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Add a binding in the current environment.
    pub fn add_bind(&mut self, variable: A, base_ty: BaseTy, predicate: Predicate<A>) {
        self.env.push(Bind {
            variable,
            base_ty,
            predicate,
        });
    }

    /// Add a constraint to be emitted later.
    pub fn add_constraint(
        &mut self,
        env: Vec<A>,
        base_ty: BaseTy,
        lhs: Predicate<A>,
        rhs: Predicate<A>,
        span: S,
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

impl<A: Emit + Copy + Ord, S: std::fmt::Debug> Emitter<A, S> {
    /// Emit all the constraints into a file.
    pub fn emit(self) -> io::Result<()> {
        let mut file = std::fs::File::create("./output.fq")?;
        // The index of the binding for each variable.
        let mut vars = BTreeMap::new();

        // First we emit all the environment bindings.
        for (index, bind) in self.env.into_iter().enumerate() {
            // Store the index for the variable.
            vars.insert(bind.variable, index);

            // Bindings are emitted with this format:
            // `bind <index> : { <variable> : <base_ty> | <predicate>}`.
            write!(file, "bind {} ", index)?;
            bind.variable.emit(&mut file)?;
            write!(file, " : {{")?;
            Variable::<A>::Bound.emit(&mut file)?;
            write!(file, ": ")?;
            bind.base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            bind.predicate.emit(&mut file)?;
            writeln!(file, "}}")?;
        }

        for (id, constraint) in self.constraints.into_iter().enumerate() {
            println!(
                "Emitting constraint {} with span {:?}.",
                id, constraint.span
            );

            writeln!(file, "\nconstraint:")?;

            // The `env` field  has the format `env [<index> ; ...]` where `index` ranges over the
            // indices of the binding for each variable in the environment of the constraint.
            write!(file, "\tenv [")?;
            let mut env = constraint.env.into_iter();
            if let Some(var) = env.next() {
                write!(file, "{}", vars[&var])?;
                for var in env {
                    write!(file, "; {}", vars[&var])?;
                }
            }
            writeln!(file, "]")?;

            // The `lhs` field has the format `lhs { b : <base_ty> | <lhs> }`.
            write!(file, "\tlhs {{")?;
            Variable::<A>::Bound.emit(&mut file)?;
            write!(file, ": ")?;
            constraint.base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            constraint.lhs.emit(&mut file)?;
            writeln!(file, "}}")?;

            // The `lhs` field has the format `rhs { b : <base_ty> | <lhs> }`.
            write!(file, "\trhs {{")?;
            Variable::<A>::Bound.emit(&mut file)?;
            write!(file, ": ")?;
            constraint.base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            constraint.rhs.emit(&mut file)?;
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
pub trait Emit {
    /// Emit a value into a buffer.
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()>;
}

impl<A: Emit> Emit for Predicate<A> {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            // Literals are emitted in the same way as they are displayed.
            Predicate::Lit(literal) => write!(writer, "{}", literal),
            // Literals are emitted according to their `Emit` implementation.
            Predicate::Var(variable) => variable.emit(writer),
            // Unary operations are emitted between parentheses.
            Predicate::UnaryOp(un_op, op) => {
                write!(writer, "(")?;
                un_op.emit(writer)?;
                write!(writer, " ")?;
                op.emit(writer)?;
                write!(writer, ")")
            }
            // Binary operations are emitted between parentheses.
            Predicate::BinaryOp(bin_op, op1, op2) => {
                write!(writer, "(")?;
                op1.emit(writer)?;
                write!(writer, " ")?;
                bin_op.emit(writer)?;
                write!(writer, " ")?;
                op2.emit(writer)?;
                write!(writer, ")")
            }
            // Inference variables are emitted using its index.
            Predicate::Hole(id) => write!(writer, "p{}", id.index()),
        }
    }
}

impl<A: Emit> Emit for &A {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        (*self).emit(writer)
    }
}

impl Emit for UnOp {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            // Use `not` instead of `!`.
            UnOp::Not { .. } => write!(writer, "not"),
            _ => write!(writer, "{}", self),
        }
    }
}

impl Emit for BinOp {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            // Use `<=>` instead of `==` for booleans.
            BinOp::Eq(BaseTy::Bool) => write!(writer, "<=>"),
            _ => write!(writer, "{}", self),
        }
    }
}

impl Emit for BaseTy {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let s = match self {
            BaseTy::Unit => "unit",
            BaseTy::Bool => "bool",
            // Emit all integer types as `int`.
            BaseTy::Int { .. } => "int",
        };

        write!(writer, "{}", s)
    }
}

impl<A: Emit> Emit for Variable<A> {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Variable::Bound => write!(writer, "b"),
            Variable::Local(a) => a.emit(writer),
            // All arguments should have been projected.
            Variable::Arg(_) => unreachable!(),
        }
    }
}
