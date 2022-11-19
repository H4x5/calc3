// a simple parser fuzzer
// permutes possible token configs and feeds them into the parser, testing for panics

use super::*;
use crate::lexer::unlex;

// all useful tokens
const TOKENS: &[Token] = &[
    Token::Var(Var::X),
    Token::Func(Func::Sin),   // 1arg
    Token::Func(Func::ATan2), // 2arg
    Token::Func(Func::Min),   // vararg
    Token::Char(Char::Plus),
    Token::Char(Char::Minus),
    // Token::Char(Char::Star),
    Token::Char(Char::Slash),
    // Token::Char(Char::Percent), // TODO
    Token::Char(Char::Bang),
    Token::Char(Char::Caret),
    Token::Char(Char::Comma),
    // Token::Char(Char::Underscore), // TODO
    Token::Char(Char::VBar),
    Token::Char(Char::OParen),
    Token::Char(Char::CParen),
];
const LEN: usize = TOKENS.len();

// FIXME
// TODO: multithread the fuzzing
pub fn fuzz<const MAX_LEN: u32>() {
    println!("starting fuzz to {MAX_LEN} with {LEN} tokens");
    eprintln!("starting fuzz to {MAX_LEN} with {LEN} tokens");

    for len in 0..=MAX_LEN {
        let total = LEN.pow(len);

        println!("fuzzing: {len} ({total})");
        eprintln!("fuzzing: {len} ({total})");

        for i in 0..total {
            if i % 10_000 == 0 && i != 0 {
                println!("  {i}/{total}");
            }

            let input = (0..len)
                .rev()
                .map(|j| TOKENS[(i / LEN.pow(j)) % LEN])
                .collect::<Vec<_>>();

            eprint!("  {i}: \"{}\" {input:?}\n   -> ", unlex(&input));

            match parse(&input) {
                Ok(expr) => eprintln!("{expr:?}"),
                Err(err) => eprintln!("{err:#}"),
            }
        }
    }
}
