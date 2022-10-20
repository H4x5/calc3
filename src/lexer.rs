use crate::hir::{Char, Token};
use crate::{Const, Func, Var};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("numeric literal overflow")]
    NumOverflow,
    #[error("unexpected char {0:?}")]
    UnexpectedChar(char),
}

pub fn lex(mut s: &str) -> Result<Vec<Token>, Error> {
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

fn parse_token(s: &str) -> Result<(Option<Token>, usize), Error> {
    let c1 = s.chars().next().expect("s is never empty");

    if c1.is_whitespace() {
        return Ok((None, c1.len_utf8()));
    }

    if let Some(c) = Char::parse(c1) {
        return Ok((Some(Token::Char(c)), c1.len_utf8()));
    }

    // FIXME: this doesn't work with 1.04 because 04 -> 4
    let num_len = s.chars().take_while(|&c| matches!(c, '0'..='9')).count();
    if num_len != 0 {
        return s[..num_len]
            .parse::<u64>()
            .map(|n| (Some(Token::Digits(n)), num_len))
            .map_err(|_| Error::NumOverflow);
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

    Err(Error::UnexpectedChar(c1))
}
