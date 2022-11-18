use crate::hir::{Char, Digit, Digits, Token};
use crate::{Const, Func, Var};
use anyhow::{bail, Result};
use std::array;

pub fn unlex(tokens: &[Token]) -> String {
    let mut out = String::new();

    for t in tokens {
        let s = match t {
            Token::Char(c) => c.str(),
            Token::Func(f) => f.str(),
            Token::Const(c) => c.str(),
            Token::Digits(n) => n.as_ref(),
            Token::Var(v) => v.str(),
            Token::Differential(d) => {
                out.push('d');
                d.str()
            }
        };

        out.push_str(s);
    }

    out
}

pub fn lex(mut s: &str) -> Result<Vec<Token>> {
    let mut tokens = Vec::new();

    loop {
        if s.is_empty() {
            break;
        }

        let (t, rem) = parse_token(s)?;
        s = &s[rem..];

        if let Some(t) = t {
            tokens.push(t);
        }
    }

    Ok(tokens)
}

fn parse_token(s: &str) -> Result<(Option<Token>, usize)> {
    let c1 = s.chars().next().expect("s is never empty");

    if c1.is_whitespace() {
        return Ok((None, c1.len_utf8()));
    }

    if let Some(c) = Char::parse(c1) {
        return Ok((Some(Token::Char(c)), c1.len_utf8()));
    }

    if matches!(c1, '0'..='9' | '.') {
        let mut iter = s
            .chars()
            .take_while(|c| matches!(c, '0'..='9' | '.'))
            .map(|c| Digit::parse(c as u8).unwrap())
            .fuse();
        let len = iter.clone().count();

        if len > 32 {
            bail!("numeric literals longer than 32 chars are not currently supported");
        }

        let digits = Digits(array::from_fn(|_| iter.next()));

        return Ok((Some(Token::Digits(digits)), len));
    }

    // the order here is important
    // functions take priority over variables
    // (so "atan" doesn't become as a*t*a*n)
    // ("at an" will still become that though)
    // (ie spaces are insignificant except to break up identifiers)

    if let Some((f, rem)) = Func::parse(s) {
        return Ok((Some(Token::Func(f)), rem));
    }

    if let Some((c, rem)) = Const::parse(s) {
        return Ok((Some(Token::Const(c)), rem));
    }

    if let Some((v, rem)) = Var::parse(s) {
        return Ok((Some(Token::Var(v)), rem));
    }

    if c1 == 'd' {
        if let Some((v, rem)) = Var::parse(&s[1..]) {
            return Ok((Some(Token::Differential(v)), rem + 1));
        }
    }

    bail!("unexpected char: {c1:?}")
}
