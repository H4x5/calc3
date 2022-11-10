// a simple parser fuzzer
// permutes possible token configs and feeds them into the parser, testing for panics

use super::*;
use std::panic::catch_unwind;

// all useful tokens (23)
const TOKENS: &[Token] = &[
    // Token::Const(Const::Pi),
    Token::Var(Var::X),
    // Token::Differential(Var::X),
    // Token::Digits(2),
    Token::Func(Func::Sin),
    // Token::Func(Func::ATan2),
    // Token::Func(Func::Ln),
    // Token::Func(Func::Log),
    // Token::Func(Func::Sqrt),
    // Token::Func(Func::Min),
    // Token::Char(Char::Plus),
    // Token::Char(Char::Minus),
    // Token::Char(Char::Star),
    // Token::Char(Char::Slash),
    // Token::Char(Char::Percent),
    // Token::Char(Char::Bang),
    // Token::Char(Char::Caret),
    // Token::Char(Char::Comma),
    // Token::Char(Char::VBar),
    // Token::Char(Char::Underscore),
    // Token::Char(Char::OParen),
    // Token::Char(Char::CParen),
];
const LEN: usize = TOKENS.len();

pub fn fuzz<const MAX_LEN: u32>() {
    eprintln!("starting fuzz to {MAX_LEN}");

    let mut panics = Vec::new();

    for len in 0..=MAX_LEN {
        eprintln!("fuzzing: {len}");

        let total = LEN.pow(len);

        for i in 0..total {
            let input = (0..len)
                .rev()
                .map(|j| TOKENS[(i / LEN.pow(j)) % LEN])
                .collect::<Vec<_>>();

            eprint!("  {i}: {input:?}\n   -> ");

            match catch_unwind(|| parse(&input)) {
                Ok(Ok(_)) => {}
                Ok(Err(e)) => {
                    eprintln!("{e:?}")
                }
                Err(_) => panics.push((len, i)),
            }
        }
    }

    eprintln!("\ndone!");

    let panic_count = panics.len();

    if panic_count != 0 {
        eprintln!("panics ({panic_count}):");

        for (len, i) in panics {
            eprintln!(" - {len}:{i}");
        }

        panic!("fuzz fail :(") // fail the test
    }
}

#[test]
fn test() {
    env::set_var("RUST_BACKTRACE", "0");

    fuzz::<3>();
}
