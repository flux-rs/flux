#![feature(rustc_private)]

mod emit;
mod glob_variable;

use emit::{Emit, Writer};

use liquid_rust_mir::{
    ty::{BaseTy, HoleId, Predicate, Ty, Variable},
    Span,
};

use std::{
    cell::RefCell,
    fs::File,
    io::{self, Write},
};

pub struct Emitter {
    variables: Vec<usize>,
    binds: RefCell<Vec<u8>>,
    wf: RefCell<Vec<u8>>,
    constraints: RefCell<Vec<u8>>,
    len_constraints: usize,
    len_binds: usize,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            variables: Vec::new(),
            binds: RefCell::new(Vec::new()),
            wf: RefCell::new(Vec::new()),
            constraints: RefCell::new(Vec::new()),
            len_constraints: 0,
            len_binds: 0,
        }
    }

    pub fn emit(self) -> io::Result<()> {
        let mut file = File::create("output.fq")?;
        file.write_all(b"fixpoint \"--save\"\n")?;
        file.write_all(b"fixpoint \"--eliminate=none\"\n\n")?;

        file.write_all(&self.binds.into_inner())?;
        file.write_all(b"\n")?;

        file.write_all(b"qualif QEq(v : @(0), x : @(0)): ((x == v))\n")?;
        file.write_all(b"qualif QGt(v : @(0), x : @(0)): ((x > v))\n")?;
        file.write_all(b"qualif QGte(v : @(0), x : @(0)): ((x >= v))\n")?;
        file.write_all(b"qualif QNot(v : bool): (not v)\n")?;
        file.write_all(b"qualif QEqZero(v : int): ((v == 0))\n")?;
        file.write_all(b"qualif QNeqZero(v : int): ((v != 0))\n")?;
        file.write_all(b"qualif QGtZero(v : int): ((v > 0))\n")?;
        file.write_all(b"qualif QGteZero(v : int): ((v >= 0))\n")?;
        file.write_all(b"qualif QLtZero(v : int): ((v < 0))\n")?;
        file.write_all(b"qualif QLteZero(v : int): ((v <= 0))\n")?;
        file.write_all(b"qualif QEqOne(v : int): ((v == 1))\n")?;
        file.write_all(b"qualif QBoolFalse(v : bool): (false)\n")?;
        file.write_all(b"qualif QIntFalse(v : int): (false)\n")?;
        file.write_all(b"qualif QIffLt(v :bool, x : @(0), y:@(0)): (v <=> x < y)\n\n")?;

        file.write_all(&self.wf.into_inner())?;

        file.write_all(&self.constraints.into_inner())
    }

    pub fn clear(&mut self) {
        self.variables.clear();
    }

    pub fn add_bind(&mut self, var: Variable, ty: &Ty) -> usize {
        if let Ty::Refined(base_ty, predicate) = ty {
            writeln!(
                self.binds.borrow_mut(),
                "bind {} {} : {{ b : {} | {} }}",
                self.len_binds,
                self.writer(var),
                self.writer(base_ty),
                self.writer(predicate)
            )
            .unwrap();

            let bind_id = self.len_binds;
            self.variables.push(bind_id);
            self.len_binds += 1;

            println!("added bind for {}", var);
            bind_id
        } else {
            panic!()
        }
    }

    pub fn add_constraint(
        &mut self,
        base_ty: BaseTy,
        lhs: Predicate,
        rhs: Predicate,
        span: Span,
    ) -> io::Result<()> {
        match rhs {
            Predicate::And(preds) => {
                for pred in preds {
                    self.add_constraint(base_ty, lhs.clone(), pred, span)?;
                }

                Ok(())
            }
            _ => {
                let mut buffer = self.constraints.borrow_mut();
                writeln!(buffer, "constraint:")?;

                write!(buffer, "  env [")?;
                self.variables
                    .iter()
                    .fold(io::Result::Ok(true), |first, bind_id| {
                        if !first? {
                            write!(buffer, "; ")?;
                        }
                        write!(buffer, "{}", bind_id)?;
                        Ok(false)
                    })?;
                writeln!(buffer, "]")?;

                writeln!(
                    buffer,
                    "  lhs {{ b : {} | {} }}",
                    self.writer(base_ty),
                    self.writer(lhs)
                )?;

                writeln!(
                    buffer,
                    "  rhs {{ b : {} | {} }}",
                    self.writer(base_ty),
                    self.writer(rhs)
                )?;

                writeln!(buffer, "  id {} tag []", self.len_constraints)?;

                self.len_constraints += 1;

                writeln!(buffer)
            }
        }
    }

    pub fn add_wf(&mut self, base_ty: BaseTy, hole_id: HoleId, bind_id: usize) -> io::Result<()> {
        let mut buffer = self.wf.borrow_mut();

        writeln!(buffer, "wf:")?;

        write!(buffer, "  env [")?;
        self.variables.iter().filter(|id| **id != bind_id).fold(
            io::Result::Ok(true),
            |first, bind_id| {
                if !first? {
                    write!(buffer, "; ")?;
                }
                write!(buffer, "{}", bind_id)?;
                Ok(false)
            },
        )?;
        writeln!(buffer, "]")?;

        writeln!(
            buffer,
            "  reft {{ b : {} | {} }}",
            self.writer(base_ty),
            self.writer(hole_id),
        )?;

        writeln!(buffer)
    }

    fn writer<'e, T: Emit>(&'e self, inner: T) -> Writer<'e, T> {
        Writer {
            emitter: self,
            inner,
        }
    }
}
