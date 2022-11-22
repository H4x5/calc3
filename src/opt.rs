use crate::{Expr, RawExpr};

macro_rules! opts {
    ( $(
    #[doc = $doc:literal]
    $opt:ident: {
        $( $in1:tt $(($($in2:tt)+))? => $out1:tt $(($($out2:tt)+))?, )+
    }
    )+ ) => {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub enum Opt {
            $( #[doc = $doc] $opt, )+
        }

        // intellij highlights `out` but not `in` (likely because `out` is expr ctx vs `in` is pat ctx)
        // this uses `in` in expr ctx to get the highlighting
        const _: () = { $( $( opts!(@render $in1 $(($($in2)+))?); )+ )+ };

        impl Opt {
            #[allow(illegal_floating_point_literal_pattern)] // FIXME
            pub fn apply(self, expr: Expr) -> Expr {
                match self {
                    $( Self::$opt => match expr {
                        $( opts!(@pat $in1 $(($($in2)+))?) => opts!(@pat $out1 $(($($out2)+))?), )+
                        _ => expr,
                    }, )+
                }
            }
        }
    };

    (@pat $x:tt) => { $x };
    (@pat $op:tt ($($x:tt $(($($rest:tt)+))?),+ $(,)?)) => {
        Expr(box RawExpr::$op($(opts!(@pat $x $(($($rest)+))?),)+))
    };

    // hack to get intellij to highlight the variants in purple :)
    (@render $x:tt) => {};
    (@render $op:tt ($($x:tt $(($($rest:tt)+))?),+ $(,)?)) => {
        let _ = RawExpr::<()>::$op;
        $( opts!(@render $x $(($($rest)+))?); )+
    };
}

opts! {
    /// universally applicable
    Univ: {
        Neg(Neg(x)) => x, // --x => x
        Neg(Sub(x, y)) => Sub(y, x), // -(x-y) => y-x
        Add(x, Neg(y)) => Sub(x, y), // x+(-y) => x-y
        Add(Neg(x), y) => Sub(y, x), // -x+y => y-x
        Div(Lit(1.0), Div(Lit(1.0), x)) => x, // 1/(1/x) => x
    }

    /// style
    Style: {
        Mul(Var(v), Lit(n)) => Mul(Lit(n), Var(v)),
    }
}
