use crate::formula::atomic_proposition::AtomicProposition;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Literal {
    True,
    False,
    Positive(AtomicProposition),
    Negative(AtomicProposition),
}

impl Literal {
    pub fn negated(self) -> Self {
        match self {
            Literal::True => Literal::False,
            Literal::False => Literal::True,
            Literal::Positive(ap) => Literal::Negative(ap),
            Literal::Negative(ap) => Literal::Positive(ap),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::True => write!(f, "⊤"),
            Literal::False => write!(f, "⊥"),
            Literal::Positive(ap) => write!(f, "{}", ap),
            Literal::Negative(ap) => write!(f, "¬{}", ap),
        }
    }
}
