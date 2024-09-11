use crate::clean::formula::atomic_proposition::AtomicProposition;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Literal {
    True,
    False,
    Atom(AtomicProposition),
}

impl Literal {
    pub fn negated(self) -> Self {
        match self {
            Literal::True => Literal::False,
            Literal::False => Literal::True,
            Literal::Atom(ap) => Literal::Atom(AtomicProposition {
                name: ap.name,
                negated: !ap.negated,
            }),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::True => write!(f, "⊤"),
            Literal::False => write!(f, "⊥"),
            Literal::Atom(ap) => write!(f, "{}", ap),
        }
    }
}
