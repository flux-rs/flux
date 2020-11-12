#![feature(try_blocks)]
#![feature(rustc_private)]
extern crate rustc_ast;

use std::{
    env,
    error::Error,
    fs::File,
    io::{prelude::*, BufReader},
};

use liquid_rust::cps_ref::{
    context::{Arena, LiquidRustCtxt},
    liquid::LiquidSolver,
    parser::FnParser,
    typeck::TypeCk,
};
use rustc_ast::attr::with_default_session_globals;

fn main() -> std::io::Result<()> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        println!("Missing file path");
        std::process::exit(1);
    }

    let file = File::open(&args[1])?;
    let mut buf_reader = BufReader::new(file);
    let mut contents = String::new();
    buf_reader.read_to_string(&mut contents)?;

    with_default_session_globals(|| {
        let arena = Arena::default();
        let cx = LiquidRustCtxt::new(&arena);
        let r: Result<bool, Box<dyn Error>> = try {
            let parsed = FnParser::new().parse(&cx, &contents)?;
            let (c, kvars) = TypeCk::cgen(&cx, &parsed)?;
            LiquidSolver::new()?.check(&c, &kvars)?
        };
        match r {
            Ok(b) => println!("{:}", if b { "Safe" } else { "Unsafe" }),
            Err(e) => println!("{:#}", e),
        }
    });
    Ok(())
}
