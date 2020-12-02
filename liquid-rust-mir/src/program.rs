use std::fmt;

use crate::{
    func::{Func, FuncId},
    statement::Statement,
};

use liquid_rust_common::index::{Index, IndexMap, IndexMapBuilder};

pub struct Program<V> {
    functions: IndexMap<FuncId, Func<V>>,
}

impl<V> Program<V> {
    pub fn builder(functions_len: usize) -> ProgramBuilder<V> {
        ProgramBuilder {
            functions: FuncId::index_map_builder(functions_len),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (FuncId, &Func<V>)> {
        self.functions.iter()
    }

    pub fn get_func(&self, func_id: FuncId) -> &Func<V> {
        self.functions.get(func_id)
    }
}

impl<V: fmt::Display> fmt::Display for Program<V> {
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

            for (bb_id, bb) in func.bblocks() {
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

pub struct ProgramBuilder<V> {
    functions: IndexMapBuilder<FuncId, Func<V>>,
}

impl<V> ProgramBuilder<V> {
    pub fn add_func(&mut self, func_id: FuncId, func: Func<V>) -> bool {
        self.functions.insert(func_id, func)
    }

    pub fn func_ids(&self) -> impl Iterator<Item = FuncId> {
        self.functions.keys()
    }

    pub fn build(self) -> Result<Program<V>, FuncId> {
        Ok(Program {
            functions: self.functions.build()?,
        })
    }
}
