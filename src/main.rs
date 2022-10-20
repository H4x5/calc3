#![feature(try_trait_v2, try_trait_v2_residual, try_blocks, iterator_try_collect)]
#![allow(dead_code, unused_variables)]
#![deny(unsafe_code)]

//! calc3
//!
//! pipeline:
//! - raw string input => lexer => HIR (`Vec<Token>`)
//! - HIR => parser (`IR`) => MIR (`Expr`)

mod fuzz;
mod hir;
mod lexer;
mod mir;
mod parser;
mod types;

use self::hir::*;
use self::lexer::lex;
use self::mir::*;
use self::parser::parse;
use self::types::*;
use anyhow::{bail, Context as _, Result};
use std::env;

fn main() -> Result<()> {
    println!("----------------------------------------");
    let input = env::args().nth(1).context("bad args")?;
    println!("input: {input:?}");

    let hir = lex(&input).context("couldn't lex input")?;
    println!("HIR: {hir:?}");

    let mir = parse(&hir).context("couldn't parse input")?;
    println!("MIR: {mir:?}");

    Ok(())
}
