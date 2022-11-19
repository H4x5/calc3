#![allow(clippy::while_let_on_iterator)]

use crate::*;
use std::iter::Iterator;
use std::vec::IntoIter as VecIter;

// enables pass-based hir -> mir parsing by allowing tokens and exprs to coexist
// we are mapping sequential tokens to nested nodes
#[derive(Clone, Debug)]
enum IR {
    Token(Token),
    // expr args are IR, not exprs
    Expr(BoxExpr<IR>),
    Group(Vec<IR>),
}

impl IR {
    fn is_token(&self) -> bool {
        matches!(self, IR::Token(_))
    }
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
    let ir = IR::Group(hir.iter().copied().map(IR::Token).collect());

    // run all the passes in order, bailing if one fails
    PASSES
        .iter()
        .copied()
        .try_fold(ir, run_pass)
        .and_then(eliminate)
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
                .try_collect::<Vec<IR>>()?
                .into_iter();
            let out = cb(&mut iter)?;
            assert_eq!(iter.len(), 0, "cb didn't exhaust iter");
            Ok(IR::Group(out))
        }
    }
}

// last step. at this point, all groups should™ contain exactly one expr (and are unwrapped)
fn eliminate(ir: IR) -> Result<Expr> {
    match ir {
        IR::Token(t) => panic!("leftover token during elimination: {t:?}"),
        IR::Group(g) => {
            if g.is_empty() {
                bail!("empty group :(");
            }

            let [x]: [IR; 1] = g.try_into().expect("non-singleton vec during elimination");
            eliminate(x)
        }
        IR::Expr(e) => Ok(e.try_map(eliminate)?.into()),
    }
}

fn take_expr(iter: &mut VecIter<IR>) -> Result<IR> {
    match iter.next().context("cannot take empty expr")? {
        IR::Token(Token::Char(Char::Plus)) => take_expr(iter),
        IR::Token(Token::Char(Char::Minus)) => take_expr(iter).map(|e| expr!(Neg: e)),
        IR::Token(t) => bail!("cannot take token as expr: `{t:?}`"),
        // passthrough everything else (minus tokens)
        // NOTE: this doesn't recursively handle nested IR, `run_pass` does that for us.
        ir => Ok(ir),
    }
}

// each item in the returned vec is a comma seperated elem
// expects trailing_commas to have run before
fn take_args(ir: IR) -> Result<Vec<IR>> {
    let IR::Group(g) = ir else {
        bail!("cannot take non paren group as args: {ir:?}");
    };

    let mut out = Vec::new();
    let mut cur = Vec::new();

    for ir in g {
        if let IR::Token(Token::Char(Char::Comma)) = ir {
            out.push(IR::Group(cur));
            cur = Vec::new();
        } else {
            cur.push(ir);
        }
    }

    if !cur.is_empty() {
        out.push(IR::Group(cur));
    }

    Ok(out)
}

// returns IR::{Group, Expr} untouched, errors on IR::Token
fn check_expr(ir: &IR) -> Result<()> {
    if let IR::Token(t) = ir {
        bail!("cannot take token as expr: `{t:?}`");
    }

    Ok(())
}

// ===== PASSES =====

#[allow(clippy::type_complexity)]
const PASSES: &[fn(&mut VecIter<IR>) -> Result<Vec<IR>>] = &[
    // Token::{Const, Var, Differential, Digits} -> Expr::{Const, Var, Differential, Lit}
    literals, // Char::{OParen, CParen, VBar} -> IR::Group, Expr::Abs
    groups,   // ~Char::Comma
    // trailing_commas, // FIXME
    // Token::Func -> Expr::__
    functions,  // Char::Bang -> Expr::Factorial
    factorials, // Char::Caret -> Expr::Pow
    exponents,  // Char::{Star, Slash} -> Expr::{Mul, Div}
    mul_div,    // Char::{Plus, Minus} -> Expr::{Add, Neg}
    add_sub,
];

fn literals(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();

    for ir in iter {
        out.push(match ir {
            IR::Token(Token::Var(v)) => expr!(Var: v),
            IR::Token(Token::Const(c)) => expr!(Const: c),
            IR::Token(Token::Differential(d)) => expr!(Differential: d),
            IR::Token(Token::Digits(d)) => expr!(Lit: d.as_ref().parse().unwrap()),
            _ => ir,
        });
    }

    Ok(out)
}

fn groups(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum Kind {
        Full,
        Paren,
        Abs,
    }

    fn take_group(iter: &mut VecIter<IR>, kind: Kind) -> Result<Vec<IR>> {
        let mut out = Vec::new();

        loop {
            let ir = match iter.next() {
                Some(x) => x,
                None if kind == Kind::Full => return Ok(out),
                None => bail!("expected more tokens to finish {kind:?} group"),
            };

            out.push(if let IR::Token(Token::Char(c)) = ir {
                match c {
                    Char::OParen => IR::Group(take_group(iter, Kind::Paren)?),

                    Char::CParen if kind == Kind::Paren => return Ok(out),
                    Char::CParen => bail!("unexpected {ir:?}"),

                    Char::VBar if kind == Kind::Abs => return Ok(vec![expr!(Abs: IR::Group(out))]),
                    Char::VBar => IR::Group(take_group(iter, Kind::Abs)?),

                    _ => ir,
                }
            } else {
                ir
            });
        }
    }

    take_group(iter, Kind::Full)
}

// eliminates trailing commas in groups to enable exprs like sin(x+1,)
// side effect: allows `6 * (7 + 8,)`, but that isn't a big deal
fn trailing_commas(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = iter.collect::<Vec<_>>();

    while let Some(IR::Token(Token::Char(Char::Comma))) = out.last() {
        out.pop();
    }

    Ok(out)
}

fn functions(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();

    macro_rules! thing {
        (match $ir:ident {
            $( $f:ident $(=> $g:ident)?: $kind:tt ),+
            $(,)?
        }) => {
            match $ir {
                IR::Token(Token::Func(f)) => match f {
                    $( Func::$f => thing!(@expr, $f, $($g,)? $kind), )+
                },
                ir => ir,
            }
        };

        (@expr, $f:ident, 1_arg) => {
            expr!($f: take_expr(iter).with_context(|| format!("malformed arg for {:?} function", Func::$f))?)
        };

        (@expr, $f:ident, 2_arg) => {{
            let next = iter.next().context("cannot take empty args")?;
            let [x, y]: [IR; 2] = take_args(next)?
                .try_into()
                .map_err(|args: Vec<IR>| anyhow!("expected 2 args for {:?}, got {}", Func::$f, args.len()))?;
            expr!($f: x, y)
        }};

        (@expr, $f:ident, vararg) => {{
            let args = take_args(iter.next().context("cannot take empty args")?)?;
            ensure!(!args.is_empty(), "vararg function {:?} requires at least 1 arg", Func::$f);
            expr!($f: args)
        }};

        (@expr, $f:ident, $g:ident, x_is_e) => {
            expr!($g: expr!(Const: Const::E), take_expr(iter)?)
        };

        (@expr, $f:ident, $g:ident, x_is_2) => {
            expr!($g: expr!(Lit: 2.0), take_expr(iter)?)
        };

        (@expr, $f:ident, $g:ident, x_is_3) => {
            expr!($g: expr!(Lit: 3.0), take_expr(iter)?)
        };
    }

    while let Some(ir) = iter.next() {
        out.push(thing! {
            match ir {
                Factorial: 1_arg,
                ATan2: 2_arg,
                ASin: 1_arg,
                ACos: 1_arg,
                ATan: 1_arg,
                ACsc: 1_arg,
                ASec: 1_arg,
                ACot: 1_arg,
                Root: 2_arg,
                Sqrt => Root: x_is_2,
                Cbrt => Root: x_is_3,
                Sgn: 1_arg,
                Add: 2_arg,
                Sub: 2_arg,
                Mul: 2_arg,
                Div: 2_arg,
                Pow: 2_arg,
                Log: 2_arg,
                Exp => Pow: x_is_e,
                Abs: 1_arg,
                Neg: 1_arg,
                Sin: 1_arg,
                Cos: 1_arg,
                Tan: 1_arg,
                Csc: 1_arg,
                Sec: 1_arg,
                Cot: 1_arg,
                Min: vararg,
                Max: vararg,
                Ln => Root: x_is_e,
            }
        });
    }

    Ok(out)
}

fn factorials(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();
    let mut prev = None;

    while let Some(ir) = iter.next() {
        if let IR::Token(Token::Char(Char::Bang)) = ir {
            if let Some(x) = prev {
                check_expr(&x).context("malformed arg for suffix operator `!`")?;
                prev = Some(expr!(Factorial: x));
            } else {
                bail!("missing arg for suffix operator `!`");
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

fn exponents(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();
    let mut prev = None;

    while let Some(ir) = iter.next() {
        if let IR::Token(Token::Char(Char::Caret)) = ir {
            if let Some(x) = prev {
                check_expr(&x).context("malformed lhs for infix operator `^`")?;
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

fn mul_div(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let mut out = Vec::new();
    let mut prev = None;

    while let Some(ir) = iter.next() {
        if let IR::Token(Token::Char(Char::Star)) = ir {
            if let Some(x) = prev {
                check_expr(&x).context("malformed lhs for infix operator `*`")?;
                let y = take_expr(iter).context("malformed rhs for infix operator `*`")?;
                prev = Some(expr!(Mul: x, y));
            } else {
                bail!("missing lhs for infix operator `*`");
            }
        } else if let IR::Token(Token::Char(Char::Slash)) = ir {
            if let Some(x) = prev {
                check_expr(&x).context("malformed lhs for infix operator `/`")?;
                let y = take_expr(iter).context("malformed rhs for infix operator `/`")?;
                prev = Some(expr!(Div: x, y));
            } else {
                bail!("missing lhs for infix operator `/`");
            }
        } else if let Some(x) = prev {
            // this is the implied multiplication
            if !x.is_token() && !ir.is_token() {
                prev = Some(expr!(Mul: x, ir));
            } else {
                out.push(x);
                prev = Some(ir);
            }
        } else {
            prev = Some(ir);
        }
    }

    if let Some(prev) = prev {
        out.push(prev);
    }

    Ok(out)
}

fn add_sub(iter: &mut VecIter<IR>) -> Result<Vec<IR>> {
    let Some(mut prev) = iter.next() else {
        return Ok(Vec::new())
    };
    check_expr(&prev).context("malformed lhs for add/sub")?;

    while iter.len() > 0 {
        prev = expr!(
            Add: prev,
            take_expr(iter).context("malformed rhs for add/sub")?
        );
    }

    Ok(vec![prev])
}
