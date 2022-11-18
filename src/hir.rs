use crate::{Const, Func, Var};
use std::fmt::{Debug, Formatter};

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
    /// a numeric literal (any string 0-9 | .)
    ///
    /// negatives are handled later
    Digits(Digits),
}

#[derive(Copy, Clone)]
#[repr(u8)]
pub enum Digit {
    _0 = b'0',
    _1 = b'1',
    _2 = b'2',
    _3 = b'3',
    _4 = b'4',
    _5 = b'5',
    _6 = b'6',
    _7 = b'7',
    _8 = b'8',
    _9 = b'9',
    Dot = b'.',
}

impl Digit {
    pub fn parse(c: u8) -> Option<Digit> {
        use Digit::*;

        Some(match c {
            b'0' => _0,
            b'1' => _1,
            b'2' => _2,
            b'3' => _3,
            b'4' => _4,
            b'5' => _5,
            b'6' => _6,
            b'7' => _7,
            b'8' => _8,
            b'9' => _9,
            b'.' => Dot,
            _ => return None,
        })
    }
}

// no more some after none
#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct Digits(pub [Option<Digit>; 32]);

impl AsRef<str> for Digits {
    fn as_ref(&self) -> &str {
        // S, S, N, N
        let amt = self.0.iter().copied().take_while(Option::is_some).count();

        #[allow(unsafe_code)]
        std::str::from_utf8(unsafe {
            std::slice::from_raw_parts(self as *const Self as *const u8, amt)
        })
        .unwrap()
    }
}

impl Debug for Digits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.pad(self.as_ref())
    }
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

    pub fn str(self) -> &'static str {
        use Char::*;

        match self {
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Percent => "%",
            Bang => "!",
            Caret => "^",
            Comma => ",",
            Underscore => "_",
            VBar => "|",
            OParen => "(",
            CParen => ")",
        }
    }
}
