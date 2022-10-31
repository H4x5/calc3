use crate::{Const, Var};
use std::convert::Infallible;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut, Residual, Try};

pub type BoxExpr<E> = Box<RawExpr<E>>;

#[derive(Clone)]
pub struct Expr(pub BoxExpr<Self>);

impl From<RawExpr<Expr>> for Expr {
    fn from(value: RawExpr<Expr>) -> Self {
        Expr(Box::new(value))
    }
}

impl Deref for Expr {
    type Target = RawExpr<Expr>;

    fn deref(&self) -> &RawExpr<Expr> {
        &self.0
    }
}

impl DerefMut for Expr {
    fn deref_mut(&mut self) -> &mut RawExpr<Expr> {
        &mut self.0
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

#[derive(Clone, Debug)]
pub enum RawExpr<E> {
    Lit(f64),
    Const(Const),
    Var(Var),
    Differential(Var),

    Add(E, E),
    Sub(E, E),
    Mul(E, E),
    Div(E, E),
    Mod(E, E),
    Pow(E, E),
    Factorial(E),
    Abs(E),
    Neg(E),

    Sin(E),
    Cos(E),
    Tan(E),
    Csc(E),
    Sec(E),
    Cot(E),

    ASin(E),
    ACos(E),
    ATan(E),
    ATan2(E, E),
    ACsc(E),
    ASec(E),
    ACot(E),

    // log_x(y)
    Log(E, E),
    // root_x(y)
    Root(E, E),

    Min(Vec<E>),
    Max(Vec<E>),
}

impl<E> RawExpr<E> {
    //noinspection RsNonExhaustiveMatch
    pub fn map<T>(self, mut f: impl FnMut(E) -> T) -> RawExpr<T> {
        match self.try_map::<Result<T, Infallible>>(|x| Ok(f(x))) {
            Ok(x) => x,

            // this branch is unreachable, but needed to typeck
            // it could be deleted with #![feature(exhaustive_patterns)]
            Err(e) => match e {},
        }
    }

    // this shit is awful but it works™
    pub fn try_map<R>(
        self,
        mut f: impl FnMut(E) -> R,
    ) -> <R::Residual as Residual<RawExpr<R::Output>>>::TryType
    where
        R: Try,
        R::Residual: Residual<RawExpr<R::Output>> + Residual<Vec<R::Output>>,
    {
        use RawExpr::*;

        // don't you just love coding! so much fun!
        try {
            match self {
                Lit(n) => Lit(n),
                Const(c) => Const(c),
                Var(v) => Var(v),
                Differential(d) => Differential(d),

                Add(x, y) => Add(f(x)?, f(y)?),
                Sub(x, y) => Sub(f(x)?, f(y)?),
                Mul(x, y) => Mul(f(x)?, f(y)?),
                Div(x, y) => Div(f(x)?, f(y)?),
                Mod(x, y) => Mod(f(x)?, f(y)?),
                Pow(x, y) => Pow(f(x)?, f(y)?),
                Factorial(x) => Factorial(f(x)?),
                Abs(x) => Abs(f(x)?),
                Neg(x) => Neg(f(x)?),

                Sin(x) => Sin(f(x)?),
                Cos(x) => Cos(f(x)?),
                Tan(x) => Tan(f(x)?),
                Csc(x) => Csc(f(x)?),
                Sec(x) => Sec(f(x)?),
                Cot(x) => Cot(f(x)?),

                ASin(x) => ASin(f(x)?),
                ACos(x) => ACos(f(x)?),
                ATan(x) => ATan(f(x)?),
                ATan2(x, y) => ATan2(f(x)?, f(y)?),
                ACsc(x) => ACsc(f(x)?),
                ASec(x) => ASec(f(x)?),
                ACot(x) => ACot(f(x)?),

                Log(x, y) => Log(f(x)?, f(y)?),
                Root(x, y) => Root(f(x)?, f(y)?),

                Min(v) => Min(v.into_iter().map(f).try_collect::<Vec<R::Output>>()?),
                Max(v) => Max(v.into_iter().map(f).try_collect::<Vec<R::Output>>()?),
            }
        }
    }
}
