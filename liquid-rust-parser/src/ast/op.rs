use crate::ast::Span;

/// The AST representation of unary operators over predicates.
#[derive(Debug)]
pub struct UnOp {
    pub kind: UnOpKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub enum UnOpKind {
    /// The `!` operator.
    Not,
    /// The `-` operator.
    Neg,
}

/// The AST representation of binary operators between predicates.
#[derive(Debug)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOpKind {
    /// The `+` operator.
    Add,
    /// The `-` operator.
    Sub,
    /// The `*` operator.
    Mul,
    /// The `/` operator.
    Div,
    /// The `%` operator.
    Rem,
    /// The `&&` operator.
    And,
    /// The `||` operator.
    Or,
    /// The `==` operator.
    Eq,
    /// The `!=` operator.
    Neq,
    /// The `<` operator.
    Lt,
    /// The `>` operator.
    Gt,
    /// The `<=` operator.
    Lte,
    /// The `>=` operator.
    Gte,
}
