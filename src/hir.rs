use crate::{Const, Func, Var};

#[derive(Copy, Clone, Debug)]
pub enum Token {
    /// e, pi, etc
    Const(Const),
    /// x, y, t, theta, etc
    Var(Var),
    /// dx, dy, dtheta, etc
    Differential(Var),
    /// sin, ln, sqrt, etc
    Func(Func),
    /// +, /, ^, >, etc
    Char(Char),
    /// a numeric literal (any string of digits 0-9)
    ///
    /// decimals and negatives are handled later
    // need to replace this with a static, copy type that handles preceding zeros
    // maybe add Dot to Digit? (removes a parser pass)
    Digits(u64),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Char {
    Plus,       // +
    Minus,      // -
    Star,       // *
    Slash,      // /
    Percent,    // %
    Bang,       // !
    Caret,      // ^
    Comma,      // ,
    Dot,        // .
    Underscore, // _
    VBar,       // |
    OParen,     // (
    CParen,     // )
}

// Equal,      // =
// Less,       // <
// Greater,    // >

impl Char {
    pub fn parse(c: char) -> Option<Self> {
        use Char::*;

        Some(match c {
            '+' => Plus,
            '-' => Minus,
            '*' => Star,
            '/' => Slash,
            '%' => Percent,
            '!' => Bang,
            '^' => Caret,
            ',' => Comma,
            '.' => Dot,
            '_' => Underscore,
            '|' => VBar,
            '(' => OParen,
            ')' => CParen,
            // '=' => Equal,
            // '<' => Less,
            // '>' => Greater,
            _ => return None,
        })
    }
}
