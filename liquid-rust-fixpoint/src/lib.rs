use liquid_rust_ty::{BaseTy, BinOp, Predicate, UnOp, Variable};

use std::{
    collections::BTreeMap,
    io::{self, Write},
};

struct Bind<A>(A, BaseTy, Predicate<A>);

struct Constraint<A> {
    env: Vec<A>,
    base_ty: BaseTy,
    lhs: Predicate<A>,
    rhs: Predicate<A>,
}

pub struct Emitter<A> {
    env: Vec<Bind<A>>,
    constraints: Vec<Constraint<A>>,
}

impl<A: Emit + Copy + Ord> Emitter<A> {
    pub fn new() -> Self {
        Self {
            env: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn add_bind(&mut self, variable: A, base_ty: BaseTy, predicate: Predicate<A>) {
        self.env.push(Bind(variable, base_ty, predicate));
    }

    pub fn add_constraint(
        &mut self,
        env: Vec<A>,
        base_ty: BaseTy,
        lhs: Predicate<A>,
        rhs: Predicate<A>,
    ) {
        self.constraints.push(Constraint {
            env,
            base_ty,
            lhs,
            rhs,
        });
    }

    pub fn emit(self) -> io::Result<()> {
        let mut file = std::fs::File::create("./output.fq")?;
        let mut vars = BTreeMap::new();

        for (index, Bind(var, base_ty, pred)) in self.env.into_iter().enumerate() {
            vars.insert(var, index);

            write!(file, "bind {} ", index)?;
            var.emit(&mut file)?;
            write!(file, " : {{")?;
            Variable::<A>::Bounded.emit(&mut file)?;
            write!(file, ": ")?;
            base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            pred.emit(&mut file)?;
            writeln!(file, "}}")?;
        }

        for (
            tag,
            Constraint {
                env,
                base_ty,
                lhs,
                rhs,
            },
        ) in self.constraints.into_iter().enumerate()
        {
            writeln!(file, "\nconstraint:")?;
            write!(file, "\tenv [")?;
            let mut env = env.into_iter();
            if let Some(var) = env.next() {
                write!(file, "{}", vars[&var])?;
                for var in env {
                    write!(file, "; {}", vars[&var])?;
                }
            }
            writeln!(file, "]")?;

            write!(file, "\tlhs {{")?;
            Variable::<A>::Bounded.emit(&mut file)?;
            write!(file, ": ")?;
            base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            lhs.emit(&mut file)?;
            writeln!(file, "}}")?;

            write!(file, "\trhs {{")?;
            Variable::<A>::Bounded.emit(&mut file)?;
            write!(file, ": ")?;
            base_ty.emit(&mut file)?;
            write!(file, " | ")?;
            rhs.emit(&mut file)?;
            writeln!(file, "}}")?;

            writeln!(file, "\tid {} tag []", tag)?;
        }

        Ok(())
    }
}

pub trait Emit {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()>;
}

impl<A: Emit> Emit for Predicate<A> {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Predicate::Lit(literal) => write!(writer, "{}", literal),
            Predicate::Var(variable) => variable.emit(writer),
            Predicate::UnApp(un_op, op) => {
                write!(writer, "(")?;
                un_op.emit(writer)?;
                write!(writer, " ")?;
                op.emit(writer)?;
                write!(writer, ")")
            }
            Predicate::BinApp(bin_op, op1, op2) => {
                write!(writer, "(")?;
                op1.emit(writer)?;
                write!(writer, " ")?;
                bin_op.emit(writer)?;
                write!(writer, " ")?;
                op2.emit(writer)?;
                write!(writer, ")")
            }
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
            UnOp::Not { .. } => write!(writer, "not"),
            UnOp::IntNot { .. } => write!(writer, "not"),
            UnOp::Neg { .. } => write!(writer, "-"),
        }
    }
}

impl Emit for BinOp {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let s = match self {
            BinOp::Add { .. } => "+",
            BinOp::Sub { .. } => "-",
            BinOp::Mul { .. } => "*",
            BinOp::Div { .. } => "/",
            BinOp::Rem { .. } => "%",
            BinOp::And { .. } => "&&",
            BinOp::Or { .. } => "||",
            BinOp::Eq(BaseTy::Bool) => "<=>",
            BinOp::Eq { .. } => "=",
            BinOp::Neq { .. } => "!=",
            BinOp::Lt { .. } => "<",
            BinOp::Gt { .. } => ">",
            BinOp::Lte { .. } => "<=",
            BinOp::Gte { .. } => ">=",
        };

        write!(writer, "{}", s)
    }
}

impl Emit for BaseTy {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let s = match self {
            BaseTy::Unit => "unit",
            BaseTy::Bool => "bool",
            BaseTy::Int { .. } => "int",
        };

        write!(writer, "{}", s)
    }
}

impl<A: Emit> Emit for Variable<A> {
    fn emit<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Variable::Bounded => write!(writer, "b"),
            Variable::Free(a) => a.emit(writer),
        }
    }
}
