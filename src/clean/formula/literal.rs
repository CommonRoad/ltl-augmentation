use crate::clean::formula::atomic_proposition::AtomicProposition;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
