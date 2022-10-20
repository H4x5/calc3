// potential major problem:
// big inputs will cause a large amt of recursion, which may blow out the stack.
// may run on separate thread with increased stack size

use crate::*;
use anyhow::{anyhow, ensure};
use std::fmt::Write;
use std::iter::Iterator;
use std::vec::IntoIter as VecIter;
// use thiserror::Error;

// #[derive(Debug, Error)]
// enum Error {
//     #[error("unexpected `{0:?}`")]
//     Unexpected(IR),
//     // #[error("expected `{0:?}`, instead got `{0:?}`")]
//     // ExpectedButGot(Token, Token),
//     #[error("expected more tokens")]
//     EndOfInput,
// }

// enables pass-based hir -> mir parsing by allowing tokens and exprs to coexist
// we are mapping sequential tokens to nested nodes
#[derive(Clone, Debug)]
enum IR {
    Token(Token),
    // expr args are IR, not exprs
    Expr(BoxExpr<IR>),
    Group(Vec<IR>),
}

impl From<RawExpr<IR>> for IR {
    fn from(value: RawExpr<IR>) -> Self {
        IR::Expr(Box::new(value))
    }
}

#[allow(unused_macros)]
macro_rules! expr {
    ($i:ident: $($args:expr),+ $(,)?) => {
        Into::into(RawExpr::$i($($args),+))
    };
}

pub fn parse(hir: &[Token]) -> Result<Expr> {
    let ir = IR::Group(hir.iter().map(|&t| IR::Token(t)).collect());

    // run all the passes in order, bailing if one fails
    PASSES.iter().copied().try_fold(ir, run_pass).map(eliminate)
}

// this recursively descends the tree, invoking cb on each group
// eg. for `6 * (7 + 8)`, cb will run out the outer (root) group and the inner group
fn run_pass(ir: IR, cb: fn(&mut VecIter<IR>) -> Result<Vec<IR>>) -> Result<IR> {
    match ir {
        IR::Token(_) => Ok(ir),
        IR::Expr(e) => e.try_map(|x| run_pass(x, cb)).map(IR::from),
        IR::Group(g) => {
            // call run recursively for each elem, then invoke cb with the group
            let mut iter = g
                .into_iter()
                // map -> collect -> into_iter to bail if err and eagerly evaluate map (basically try_map)
                // also we need a VecIter (from Vec::into_iter) to pass into cb
                .map(|x| run_pass(x, cb))
                .collect::<Result<Vec<_>>>()?
                .into_iter();
            let out = cb(&mut iter)?;
            assert_eq!(iter.len(), 0, "cb didn't exhaust iter");
            Ok(IR::Group(out))
        }
    }
}

// last step. at this point, all groups should™ contain exactly one expr (and are unwrapped)
fn eliminate(ir: IR) -> Expr {
    // FIXME: remove
    if cfg!(test) {
        eprintln!("{ir:?}");
        return Expr::from(RawExpr::Differential(Var::Theta)); // dummy (ignored)
    }

    match ir {
        IR::Token(t) => panic!("leftover token during elimination: {t:?}"),
        IR::Group(g) => {
            if g.is_empty() {
                todo!("this branch is possible but unimplemented");
            }

            let [x]: [IR; 1] = g.try_into().expect("non-singleton vec during elimination");
            eliminate(x)
        }
        IR::Expr(e) => e.map(eliminate).into(),
    }
}

fn take_expr(iter: &mut VecIter<IR>) -> Result<IR> {
    match iter.next().context("cannot take empty expr")? {
        IR::Token(Token::Char(Char::Plus)) => take_expr(iter),
        IR::Token(Token::Char(Char::Minus)) => take_expr(iter).map(|e| expr!(Neg: e)),
        IR::Token(t) => bail!("cannot take token as expr: `{t:?}`"),
        // IR::Token(t) => panic!("take_expr called before eliminating non-char tokens: `{t:?}`"),
        // passthrough everything else (minus tokens)
        // NOTE: this doesn't recursively handle nested IR, `run_pass` does that for us.
        ir => Ok(ir),
    }
}

// each item in the returned vec is a comma seperated elem
// expects trailing_commas to have run before
fn take_args(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();

    loop {
        match iter.next() {
            Some(IR::Token(Token::Char(Char::Comma))) => {
                out.push(IR::Group(cur));
                cur = Vec::new();
            }
            Some(ir) => out.push(ir),
            None => {
                out.push(IR::Group(cur));
                return Ok(out);
            }
        }
    }
}

// returns IR::{Group, Expr} untouched, errors on IR::Token
fn check_expr(ir: IR) -> Result<IR> {
    match ir {
        IR::Token(t) => bail!("check_expr fail: {t:?}"),
        _ => Ok(ir),
    }
}

// ===== PASSES =====

#[allow(clippy::type_complexity)]
const PASSES: &[fn(&mut VecIter<IR>) -> Result<Vec<IR>>] = &[
    // Token::{Const, Var, Differential} -> Expr::{Const, Var, Differential}
    literals,
    // Token::Digits, Char::Dot -> Expr::Lit
    numbers,
    // Char::{OParen, CParen, VBar} -> IR::Group, Expr::Abs
    // groups,
    // ~Char::Comma
    trailing_commas,
    // Token::Func -> Expr::__
    functions,
    // Char::Bang -> Expr::Factorial
    // factorials,
    // Char::Caret -> Expr::Pow
    // exponents,
    // Char::{Star, Slash} -> Expr::{Mul, Div}
    // mul_div,
    // FIXME: plus/minus passes
    // ~Char::{Plus, Minus} -> Expr::{Add, Sub}
    // add_sub,
    // Char::{Plus, Minus} -> Expr::Neg
    // pos_neg,
];

fn literals(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    Ok(iter
        .map(|ir| match ir {
            IR::Token(Token::Var(v)) => expr!(Var: v),
            IR::Token(Token::Const(c)) => expr!(Const: c),
            IR::Token(Token::Differential(d)) => expr!(Differential: d),
            _ => ir,
        })
        .collect())
}

fn numbers(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();
    let mut prev = None;

    // FIXME: run this on prev after iter exhaust
    while let Some(ir) = iter.next() {
        let lhs = match prev.take() {
            Some(IR::Token(Token::Digits(n))) => Some(n),
            Some(prev) => {
                out.push(prev);
                None
            }
            None => None,
        };

        let rhs = match ir {
            IR::Token(Token::Char(Char::Dot)) => match iter.next() {
                Some(IR::Token(Token::Digits(n))) => Some(n),
                // lone dot
                _ if lhs.is_none() => bail!("unexpected `{:?}`", Token::Char(Char::Dot)),
                Some(next) => {
                    prev = Some(next);
                    None
                }
                None => None,
            },
            _ => {
                prev = Some(ir);
                None
            }
        };

        if lhs.is_none() && rhs.is_none() {
            continue;
        }

        let mut fmt = String::new();

        if let Some(n) = lhs {
            write!(fmt, "{n}").unwrap();
        }
        if let Some(n) = rhs {
            write!(fmt, ".{n}").unwrap();
        }

        let n: f64 = fmt
            .parse()
            .with_context(|| format!("invalid float literal: ({lhs:?}, {rhs:?})"))?;

        out.push(expr!(Lit: n));
    }

    if let Some(last) = prev {
        out.push(match last {
            IR::Token(Token::Char(Char::Dot)) => bail!("unexpected `{last:?}`"),
            IR::Token(Token::Digits(n)) =>
                expr!(Lit: format!("{n}").parse().context("invalid float literal: (Some({n}), None)")?),
            _ => last,
        });
    }

    Ok(out)
}

fn groups(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    todo!()
}

// eliminates trailing commas in groups to enable exprs like sin(x+1,)
// side effect: allows `6 * (7 + 8,)`, but that isn't a big deal
fn trailing_commas(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = iter.collect::<Vec<_>>();

    if let Some(IR::Token(Token::Char(Char::Comma))) = out.last() {
        out.pop();
    }

    Ok(out)
}

fn functions(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();

    while let Some(ir) = iter.next() {
        out.push(match ir {
            IR::Token(Token::Func(f)) => match f {
                Func::Sin => expr!(Sin: take_expr(iter)?),
                Func::Cos => expr!(Cos: take_expr(iter)?),
                Func::Tan => expr!(Tan: take_expr(iter)?),
                Func::Csc => expr!(Csc: take_expr(iter)?),
                Func::Sec => expr!(Sec: take_expr(iter)?),
                Func::Cot => expr!(Cot: take_expr(iter)?),
                Func::ASin => expr!(ASin: take_expr(iter)?),
                Func::ACos => expr!(ACos: take_expr(iter)?),
                Func::ATan => expr!(ATan: take_expr(iter)?),
                Func::ATan2 => {
                    let [x, y]: [IR; 2] = take_args(iter)?
                        .try_into()
                        .map_err(|g| anyhow!("expected 2 args for atan2, got {g:?}"))?;
                    expr!(ATan2: x, y)
                }
                Func::ACsc => expr!(ACsc: take_expr(iter)?),
                Func::ASec => expr!(ASec: take_expr(iter)?),
                Func::ACot => expr!(ACot: take_expr(iter)?),
                Func::Ln => expr!(Log: expr!(Const: Const::E), take_expr(iter)?),
                Func::Log => {
                    let [x, y]: [IR; 2] = take_args(iter)?
                        .try_into()
                        .map_err(|args| anyhow!("expected 2 args for log, got {args:?}"))?;
                    expr!(Log: x, y)
                }
                Func::Sqrt => expr!(Root: expr!(Lit: 2.0), take_expr(iter)?),
                Func::Cbrt => expr!(Root: expr!(Lit: 3.0), take_expr(iter)?),
                Func::Min => {
                    let args = take_args(iter)?;
                    ensure!(!args.is_empty(), "max requires >= 1 arg");
                    expr!(Min: args)
                }
                Func::Max => {
                    let args = take_args(iter)?;
                    ensure!(!args.is_empty(), "max requires >= 1 arg");
                    expr!(Max: args)
                }
                Func::Abs => expr!(Abs: take_expr(iter)?),
            },
            _ => ir,
        });
    }

    Ok(out)
}

// ===== OLD SHIT =====

// ===== NOTES =====
// dont forget PEMDAS!
// (or GF!NEMDAS!) (group, function, factorial, negative, exponent, mul/div, add/sub)
// how to parse 3/4+5^6-7*(8+9)?
// - still need some recursion for paren handling
// - is implied multiplication always the same as explicit multiplication?
// - negative higher precedence than factorial
// - factorial higher precedence than exp
// - lookaheads?
// - sequentially or in prio passes?
// - passes eliminated recursive calls
// - functions as operators with precedence
// - |x| -> |(x)| (logically)
// - pass priority for pemdas
// - grouping symbols (everything inside parsed as its own expr)
// - what abt |x + |y + 7|^3|
//   - vbar groups aren't always sequential
//   - could parse it as a recursive group requiring another vbar at the end
//   - RESOLUTION: when in a vbar group, another vbar unconditionally ends it.
//     when not in a vbar group, a vbar unconditionally starts a vbar group.
//     thus, to get the desired result, type |x + (|y + 7|)^3|.
//   - NOTE: this may be possible depending on how take_expr & take_group semantics work
//
// is a+b+c add(a, add(b, c)) or add(add(a, b), c)?
// i think first
// just because of how exprs get parsed
//
// in order to handle things like operator precedence, we run multiple passes on the HIR.
// passes (PEMDAS):
// - grouping symbols (parens, abs vbars `|`)
// - ~ functions
// - factorial suffix operator `!`
// REMOVED: negative prefix operator `-` (happens implicitly during take_expr and maybe at the end)
// - exponents `^`z
// - multiplication `*` and division `/`
// - addition `+` and subtraction `-`
// - prefix neg op
//
// -5! is -(5!) not (-5)!
//   ie factorial is stronger than negatives
// what abt sin -5!
// sin -5 -> sin(-5)
// sin -5! -> sin(-5)!
// -5! -> -(5!)
// ^ this is possible when negatives are parsed with take_expr

#[derive(Copy, Clone, Eq, PartialEq)]
enum GroupKind {
    // (x)
    Paren,
    // |x|
    Abs,
    // x
    Full,
}

// precedence level 1: groups (paren and abs)
// is recursive for nested groups
// handles comma seperated paren args
// eliminates every Char::{OParen, CParen, VBar}
//
// 8*(9+10) -> `(8 * (9 + 10))`
// 5+(6*(7+4))+9 -> `(5 + (6 * (7 + 4)) + 9)`
// atan2(x+4, y) -> `(atan2 (x + 4 , y))`
#[cfg(FALSE)]
fn group(ir: &mut impl Iterator<Item = IR>, kind: GroupKind) -> Result<IR> {
    let mut g = Vec::new();

    loop {
        let i = match ir.next() {
            Some(x) => x,
            None if kind == GroupKind::Full => return Ok(IR::Group(g)),
            None => bail!(Error::EndOfInput),
        };

        g.push(if let IR::Token(Token::Char(c)) = i {
            match c {
                Char::OParen => group(ir, GroupKind::Paren)?,

                Char::CParen if kind == GroupKind::Paren => return Ok(IR::Group(g)),
                Char::CParen => bail!(Error::Unexpected(i)),

                Char::VBar if kind == GroupKind::Abs => return Ok(IR::Group(g)),
                Char::VBar => group(ir, GroupKind::Abs)?,

                _ => i,
            }
        } else {
            i
        });
    }
}

// ALL ACTUAL PASSES:
// - basic literals: Token::{Const, Var, Differential} -> Expr::{Const, Var, Differential}
// - (positive) numeric literals: Char::Dot, Token::Digits -> Expr::Lit
// - groups: Char::{OParen, CParen, VBar} -> IR::Group, Expr::Abs
// - (maybe trailing comma elim)
// - functions: Token::Func, Char::Comma -> Expr::__
// ops:
// - factorial: Char::Bang -> Expr::Factorial
// - exponents: Char::Caret -> Expr::Pow
// - mul/div: Char::{Star, Slash} -> Expr::{Mul, Div}
// - add/sub: Char::{Plus, Minus} -> Expr::{Add, Sub}
// finale:
// - elimination (IR -> Expr)

// function parsing:
// - single arg: take_expr
// - multi arg: take_args, verify correct amt
// - vararg: take_args

// take_expr:
// takes first IR
// if Char::Minus, add Expr::Neg(_) and repeat until non-Char::Minus
// if Char::Plus, ignore (sin +x -> sin x)
// if any other Char, error

// Thoughts: could take_expr parse abs/paren groups?
// this is going back towards sequential parsing and may not work
// also I like the pass based model more, both conceptually and to implement
// I think no, overcomplicated things and defeats the group priority stuff (kinda?)
// ======
// ALSO: we only take_expr for the rhs, never for lhs
// this means -5^2 -> -(5^2)
// and 5^-2 -> 5^(-2)
// which I think is a good thing
// NOTE: how does this work with leftover neg prefix ops?
//   do we run one last "remaining neg op" pass? maybe

// take_args:
// splits a group by commas
// (6 + 7 , 9 , 14 ^ 2) -> [(6 + 7), (9), (14 ^ 2)]
// IR::Group: Char::Comma -> Vec<IR::Group>

// IR::Token could just be IR::{Char, Func}? (if first 2 passes can happen before everything else)
// maybe no? too confusing...
// we are converting from sequential tokens to nested Exprs
// groups represent the (nested) sequential
// at the end, all groups should™ contain exactly one expr (and can be unwrapped)
// R: No

// eliminates Token::Char(Char::{OParen, CParen, VBar})
fn group2(ir: IR) -> Result<IR> {
    enum Mode {
        Paren,
        Abs,
        Full,
    }

    fn tokens(t: &mut impl Iterator<Item = IR>, mode: Mode) -> Result<IR> {
        todo!()
    }

    match ir {
        IR::Group(g) => tokens(&mut g.into_iter(), Mode::Full),
        _ => todo!(),
    }
}

// ops passes. these work on sequential tokens, invoking a transformation callback on each group.
#[cfg(FALSE)]
mod seq_pass {
    use super::*;

    // FIXME: abstract out similar logic here

    // factorial `!`
    fn factorial(iter: &mut dyn Iterator<Item = IR>) -> Result<Vec<IR>> {
        let mut out = Vec::new();
        let mut prev = None;

        while let Some(ir) = iter.next() {
            if let IR::Token(Token::Char(Char::Bang)) = ir {
                if let Some(x) = prev {
                    // FIXME: verify x is not a token
                    prev = Some(expr!(Factorial: x));
                } else {
                    bail!("missing target for suffix operator `!`");
                }
            } else if let Some(x) = prev.replace(ir) {
                out.push(x);
            }
        }

        Ok(out)
    }

    // exponents `^`
    fn exp(iter: &mut dyn Iterator<Item = IR>) -> Result<Vec<IR>> {
        let mut out = Vec::new();
        let mut prev = None;

        while let Some(ir) = iter.next() {
            if let IR::Token(Token::Char(Char::Caret)) = ir {
                if let Some(x) = prev {
                    // FIXME: verify x is not a token
                    let y = take_expr(iter).context("malformed rhs for infix operator `^`")?;
                    prev = Some(expr!(Pow: x, y));
                } else {
                    bail!("missing lhs for infix operator `^`");
                }
            } else if let Some(x) = prev.replace(ir) {
                out.push(x);
            }
        }

        if let Some(prev) = prev {
            out.push(prev);
        }

        Ok(out)
    }

    // multiplication `*` and division `/`
    fn mul_div(iter: &mut dyn Iterator<Item = IR>) -> Result<Vec<IR>> {
        let mut out = Vec::new();
        let mut prev = None;

        while let Some(ir) = iter.next() {
            if let IR::Token(Token::Char(Char::Star)) = ir {
                if let Some(x) = prev {
                    // FIXME: verify x is not a token
                    let y = take_expr(iter).context("malformed rhs for infix operator `*`")?;
                    prev = Some(expr!(Mul: x, y));
                } else {
                    bail!("missing lhs for infix operator `*`");
                }
            } else if let IR::Token(Token::Char(Char::Slash)) = ir {
                if let Some(x) = prev {
                    // FIXME: verify x is not a token
                    let y = take_expr(iter).context("malformed rhs for infix operator `/`")?;
                    prev = Some(expr!(Div: x, y));
                } else {
                    bail!("missing lhs for infix operator `/`");
                }
            } else if let Some(x) = prev.replace(ir) {
                out.push(x);
            }
        }

        if let Some(prev) = prev {
            out.push(prev);
        }

        Ok(out)
    }
}
