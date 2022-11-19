#![feature(try_trait_v2, try_trait_v2_residual, try_blocks, iterator_try_collect)]
#![feature(let_else)]
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
use crate::fuzz::fuzz;
use anyhow::{anyhow, bail, ensure, Context as _, Result};
use std::env;

// FIXME
fn main() -> Result<()> {
    // cargo run --release 2> out.txt
    env::set_var("RUST_BACKTRACE", "0");

    fuzz::<6>();

    // println!("----------------------------------------");
    // let input = env::args().nth(1).context("bad args")?;
    // println!("input: {input}");
    //
    // let hir = lex(&input).context("couldn't lex input")?;
    // println!("HIR: {hir:?}");
    //
    // let mir = parse(&hir).context("couldn't parse input")?;
    // println!("MIR: {mir:?}");

    Ok(())
}
