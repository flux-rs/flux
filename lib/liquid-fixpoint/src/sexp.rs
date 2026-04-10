use std::str::Chars;

#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    S(String),
    Q(String),
    I(i128),
    F(f64),
    B(bool),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Sexp {
    Atom(Atom),
    List(Vec<Sexp>),
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedEOF,
    InvalidToken(String),
    UnclosedString,
    InvalidNumber(String),
}

pub struct Parser<'a> {
    chars: Chars<'a>,
    current: Option<char>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        let mut chars = input.chars();
        let current = chars.next();
        Parser { chars, current }
    }

    fn bump(&mut self) {
        self.current = self.chars.next();
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.current, Some(c) if c.is_whitespace()) {
            self.bump();
        }
    }

    pub fn parse(&mut self) -> Result<Sexp, ParseError> {
        self.skip_whitespace();
        match self.current {
            Some('(') => self.parse_list(),
            Some('"') => self.parse_quoted_string(),
            Some(_) => self.parse_atom(),
            None => Err(ParseError::UnexpectedEOF),
        }
    }

    fn parse_list(&mut self) -> Result<Sexp, ParseError> {
        self.bump(); // consume '('
        let mut items = Vec::new();

        loop {
            self.skip_whitespace();
            match self.current {
                Some(')') => {
                    self.bump(); // consume ')'
                    break;
                }
                Some(_) => {
                    let expr = self.parse()?;
                    items.push(expr);
                }
                None => return Err(ParseError::UnexpectedEOF),
            }
        }
        Ok(Sexp::List(items))
    }

    fn parse_quoted_string(&mut self) -> Result<Sexp, ParseError> {
        self.bump(); // consume '"'
        let mut result = String::new();

        while let Some(c) = self.current {
            match c {
                '"' => {
                    self.bump(); // consume closing '"'
                    return Ok(Sexp::Atom(Atom::Q(result)));
                }
                _ => {
                    result.push(c);
                    self.bump();
                }
            }
        }

        Err(ParseError::UnclosedString)
    }

    fn parse_atom(&mut self) -> Result<Sexp, ParseError> {
        let mut s = String::new();

        if self.current == Some('-') {
            s.push('-');
            self.bump();
        }

        while let Some(c) = self.current {
            if !c.is_whitespace() && c != '(' && c != ')' && c != '"' {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }

        if s.is_empty() {
            return Err(ParseError::InvalidToken("Empty atom".to_string()));
        }

        match s.as_str() {
            "true" => Ok(Sexp::Atom(Atom::B(true))),
            "false" => Ok(Sexp::Atom(Atom::B(false))),
            _ => {
                if let Ok(i) = s.parse::<i128>() {
                    Ok(Sexp::Atom(Atom::I(i)))
                } else if let Ok(f) = s.parse::<f64>() {
                    Ok(Sexp::Atom(Atom::F(f)))
                } else {
                    Ok(Sexp::Atom(Atom::S(s)))
                }
            }
        }
    }

    pub fn parse_all(&mut self) -> Result<Vec<Sexp>, ParseError> {
        let mut expressions = Vec::new();

        while self.current.is_some() {
            self.skip_whitespace();
            if self.current.is_none() {
                break;
            }

            let expr = self.parse()?;
            expressions.push(expr);
        }

        Ok(expressions)
    }
}
