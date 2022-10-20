#![allow(clippy::single_char_pattern)]

/// a mathematical constant
#[derive(Copy, Clone, Debug)]
pub enum Const {
    /// euler's number `e`
    E,
    /// pi `π`
    Pi,
    // /// tau `τ`
    // Tau,
    /// the golden ratio `φ`
    Phi,
}

impl Const {
    pub fn parse(s: &str) -> Option<(Self, usize)> {
        use Const::*;

        Some(match () {
            // _ if s.starts_with("tau") => (Tau, 3),
            _ if s.starts_with("phi") => (Phi, 3),
            _ if s.starts_with("pi") => (Pi, 2),
            _ if s.starts_with("e") => (E, 1),
            _ => return None,
        })
    }
}

/// a named variable
#[derive(Copy, Clone, Debug)]
pub enum Var {
    A,
    B,
    C,
    // d is derivatives stuff
    // e is a constant
    // f,g,h are for functions
    // i is imaginary
    N,
    R,
    T,
    X,
    Y,
    Z,

    Theta,
}

impl Var {
    pub fn parse(s: &str) -> Option<(Self, usize)> {
        use Var::*;

        Some(match () {
            _ if s.starts_with("theta") => (Theta, 5),
            _ if s.starts_with("a") => (A, 1),
            _ if s.starts_with("b") => (B, 1),
            _ if s.starts_with("c") => (C, 1),
            _ if s.starts_with("n") => (N, 1),
            _ if s.starts_with("r") => (R, 1),
            _ if s.starts_with("t") => (T, 1),
            _ if s.starts_with("x") => (X, 1),
            _ if s.starts_with("y") => (Y, 1),
            _ if s.starts_with("z") => (Z, 1),
            _ => return None,
        })
    }
}

/// any sort of named/symbol (not operator) mathematical function
#[derive(Copy, Clone, Debug)]
pub enum Func {
    Sin,
    Cos,
    Tan,
    Csc,
    Sec,
    Cot,

    ASin,
    ACos,
    ATan,
    ATan2,
    ACsc,
    ASec,
    ACot,

    Ln,
    Log,

    Sqrt,
    Cbrt,

    Min,
    Max,
    Abs,
    // Int,
}

impl Func {
    pub fn parse(s: &str) -> Option<(Self, usize)> {
        use Func::*;

        Some(match () {
            _ if s.starts_with("atan2") => (ATan2, 5),
            _ if s.starts_with("asin") => (ASin, 4),
            _ if s.starts_with("acos") => (ACos, 4),
            _ if s.starts_with("atan") => (ATan, 4),
            _ if s.starts_with("acsc") => (ACsc, 4),
            _ if s.starts_with("asec") => (ASec, 4),
            _ if s.starts_with("acot") => (ACot, 4),
            _ if s.starts_with("sqrt") => (Sqrt, 4),
            _ if s.starts_with("cbrt") => (Cbrt, 4),
            _ if s.starts_with("sin") => (Sin, 3),
            _ if s.starts_with("cos") => (Cos, 3),
            _ if s.starts_with("tan") => (Tan, 3),
            _ if s.starts_with("csc") => (Csc, 3),
            _ if s.starts_with("sec") => (Sec, 3),
            _ if s.starts_with("cot") => (Cot, 3),
            _ if s.starts_with("log") => (Log, 3),
            _ if s.starts_with("min") => (Min, 3),
            _ if s.starts_with("max") => (Max, 3),
            _ if s.starts_with("abs") => (Abs, 3),
            _ if s.starts_with("ln") => (Ln, 2),
            _ => return None,
        })
    }
}
