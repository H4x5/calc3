#[macro_export]
macro_rules! define {
    (#[doc = $tydoc:literal] enum $ty:ident {
        $( $(#[doc = $vdoc:literal])? $v:ident: $s:literal $(| $s2:literal)?, )+
    }) => {
        #[doc = $tydoc]
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        pub enum $ty {
            $( $(#[doc = $vdoc])? $v, )+
        }

        impl $ty {
            pub fn parse(s: &str) -> Option<(Self, usize)> {
                match () {
                    $(
                        () if s.starts_with($s) => Some((Self::$v, <str>::len($s))),
                        // special case for sign/sgn
                        $( () if s.starts_with($s2) => Some((Self::$v, <str>::len($s2))), )?
                    )+
                    _ => None,
                }
            }

            pub const fn str(self) -> &'static str {
                match self {
                    $( Self::$v => $s, )+
                }
            }
        }
    };
}

define! {
    /// a mathematical constant
    enum Const {
        /// the golden ratio `φ`
        Phi: "phi",

        // /// tau `τ`
        // Tau: "tau",

        /// pi `π`
        Pi: "pi",

        /// euler's number `e`
        E: "e",
    }
}

define! {
    /// a named variable
    enum Var {
        Theta: "theta",

        A: "a",
        B: "b",
        C: "c",
        N: "n",
        R: "r",
        T: "t",
        X: "x",
        Y: "y",
        Z: "z",
    }
}
