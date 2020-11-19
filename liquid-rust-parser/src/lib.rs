pub mod ast;
mod lexer;

use lexer::Lexer;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser);

pub fn parse() {
    let source = "fn(x: {x: usize | x > 0}) -> {y: usize | y > x}";
    let lexer = Lexer::new(source);
    match parser::TyParser::new().parse(source, lexer) {
        x => println!("{:?}", x),
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        super::parse();
    }
}
