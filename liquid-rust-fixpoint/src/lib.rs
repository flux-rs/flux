#![feature(rustc_private)]

mod emit;
mod glob_variable;

use emit::{Emit, Writer};
use glob_variable::GlobVariable;

use liquid_rust_common::index::{Index, IndexGen};
use liquid_rust_mir::{
    ty::{BaseTy, HoleId, LocalVariable, Predicate},
    Span,
};

use std::{cell::RefCell, collections::BTreeMap, fs::File, io::Write};

pub struct Emitter {
    var_generator: IndexGen<GlobVariable>,
    variables: BTreeMap<LocalVariable, GlobVariable>,
    binds: RefCell<Vec<u8>>,
    wf: RefCell<Vec<u8>>,
    constraints: RefCell<Vec<u8>>,
    len_constraints: usize,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            var_generator: IndexGen::new(),
            variables: BTreeMap::new(),
            binds: RefCell::new(Vec::new()),
            wf: RefCell::new(Vec::new()),
            constraints: RefCell::new(Vec::new()),
            len_constraints: 0,
        }
    }

    pub fn emit(self) {
        let mut file = File::create("output.fq").unwrap();
        file.write_all(b"fixpoint \"--save\"\n");
        file.write_all(b"fixpoint \"--eliminate=none\"\n\n");
        file.write_all(&self.binds.into_inner());
        file.write_all(b"\n");
        file.write_all(&self.wf.into_inner());
        file.write_all(&self.constraints.into_inner());
    }

    pub fn clear(&mut self) {
        self.variables.clear();
    }

    pub fn add_bind(&mut self, var: LocalVariable, base_ty: BaseTy, predicate: &Predicate) {
        let glob_var = self.var_generator.generate();

        writeln!(
            self.binds.borrow_mut(),
            "bind {} {} : {{ b : {} | {} }}",
            glob_var.index(),
            glob_var,
            self.writer(base_ty),
            self.writer(predicate)
        )
        .unwrap();

        self.variables.insert(var, glob_var);

        println!("added bind for {}", var);
    }

    pub fn add_constraint(&mut self, base_ty: BaseTy, lhs: Predicate, rhs: Predicate, span: Span) {
        match rhs {
            Predicate::And(preds) => {
                for pred in preds {
                    self.add_constraint(base_ty, lhs.clone(), pred, span);
                }
            }
            _ => {
                let mut buffer = self.constraints.borrow_mut();
                writeln!(buffer, "constraint:");

                write!(buffer, "  env [");
                self.variables.values().fold(true, |first, var| {
                    if !first {
                        write!(buffer, "; ");
                    }
                    write!(buffer, "{}", var.index());
                    false
                });
                writeln!(buffer, "]");

                writeln!(
                    buffer,
                    "  lhs {{ b : {} | {} }}",
                    self.writer(base_ty),
                    self.writer(lhs)
                );

                writeln!(
                    buffer,
                    "  rhs {{ b : {} | {} }}",
                    self.writer(base_ty),
                    self.writer(rhs)
                );

                writeln!(buffer, "  id {} tag []", self.len_constraints);

                self.len_constraints += 1;

                writeln!(buffer);
            }
        }
    }

    pub fn add_wf(&mut self, base_ty: BaseTy, hole_id: HoleId) {
        let mut buffer = self.wf.borrow_mut();

        writeln!(buffer, "wf:");

        writeln!(buffer, "  env []");

        writeln!(
            buffer,
            "  reft {{ b : {} | {} }}",
            self.writer(base_ty),
            self.writer(hole_id),
        );

        writeln!(buffer);
    }

    fn writer<'e, T: Emit>(&'e self, inner: T) -> Writer<'e, T> {
        Writer {
            emitter: self,
            inner,
        }
    }
}
