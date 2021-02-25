use std::fmt;

use crate::func::{Func, FuncId};

use liquid_rust_common::index::IndexMap;

pub struct Program {
    functions: IndexMap<FuncId, Func>,
}

impl Program {
    pub fn builder(functions_len: usize) -> ProgramBuilder {
        ProgramBuilder {
            functions: IndexMap::from_raw((0..functions_len).map(|_| None).collect()),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (FuncId, &Func)> {
        self.functions.iter()
    }

    pub fn get_func(&self, func_id: FuncId) -> &Func {
        self.functions.get(func_id).unwrap()
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

            for (bb_id, bb) in func.bblocks() {
                write!(f, "\n\t\\\\ predecessors: [")?;
                let mut predecessors = bb.predecessors().iter();
                if let Some(predecessor) = predecessors.next() {
                    write!(f, "{}", predecessor)?;
                    for predecessor in predecessors {
                        write!(f, ", {}", predecessor)?;
                    }
                }
                writeln!(f, "]")?;
                writeln!(f, "\t{}: {{", bb_id)?;

                for statement in bb.statements() {
                    writeln!(f, "\t\t{};", statement)?;
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
    functions: IndexMap<FuncId, Option<Func>>,
}

impl ProgramBuilder {
    pub fn add_func(&mut self, func_id: FuncId, func: Func) -> bool {
        self.functions
            .get_mut(func_id)
            .unwrap()
            .replace(func)
            .is_some()
    }

    pub fn func_ids(&self) -> impl Iterator<Item = FuncId> {
        self.functions.keys()
    }

    pub fn build(self) -> Result<Program, FuncId> {
        let mut functions = Vec::with_capacity(self.functions.len());

        for (func_id, func) in self.functions {
            functions.push(func.ok_or(func_id)?);
        }

        Ok(Program {
            functions: IndexMap::from_raw(functions),
        })
    }
}
