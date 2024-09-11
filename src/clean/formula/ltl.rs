use crate::clean::formula::atomic_proposition::AtomicProposition;
use crate::clean::formula::literal::Literal;
use crate::clean::formula::nnf::NNFFormula;
use crate::clean::sequence::Time;
use crate::clean::sets::interval::Interval;
use std::collections::BTreeSet;
use std::fmt::Display;
use termtree::Tree;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Formula {
    // atomic proposition + constants
    AP(AtomicProposition),
    True,
    False,

    // propositional connectives
    Not(Box<Formula>),
    And(BTreeSet<Formula>),
    Or(BTreeSet<Formula>),
    Implies(Box<Formula>, Box<Formula>),

    // temporal connectives
    Until(Box<Formula>, Interval, Box<Formula>),
    Release(Box<Formula>, Interval, Box<Formula>),
    Globally(Interval, Box<Formula>),
    Finally(Interval, Box<Formula>),
    Next(Time, Box<Formula>),
}

impl Formula {
    pub fn negated(sub: Self) -> Self {
        Formula::Not(Box::new(sub))
    }

    pub fn and(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => Formula::True,
            1 => subs.pop_first().expect("Length is 1"),
            _ => Formula::And(subs),
        }
    }

    pub fn or(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => Formula::False,
            1 => subs.pop_first().expect("Length is 1"),
            _ => Formula::Or(subs),
        }
    }

    pub fn implies(lhs: Self, rhs: Self) -> Self {
        Formula::Implies(Box::new(lhs), Box::new(rhs))
    }

    pub fn until(lhs: Self, int: Interval, rhs: Self) -> Self {
        Formula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn release(lhs: Self, int: Interval, rhs: Self) -> Self {
        Formula::Release(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn globally(int: Interval, sub: Self) -> Self {
        Formula::Globally(int, Box::new(sub))
    }

    pub fn finally(int: Interval, sub: Self) -> Self {
        Formula::Finally(int, Box::new(sub))
    }

    pub fn next(time: Time, sub: Self) -> Self {
        Formula::Next(time, Box::new(sub))
    }

    fn to_termtree(&self) -> Tree<String> {
        match self {
            Formula::AP(ap) => Tree::new(format!("{}", ap)),
            Formula::True => Tree::new("⊤".to_string()),
            Formula::False => Tree::new("⊥".to_string()),

            Formula::Not(sub) => Tree::new("¬".to_string()).with_leaves([sub.to_termtree()]),
            Formula::And(subs) => {
                Tree::new("∧".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            Formula::Or(subs) => {
                Tree::new("∨".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            Formula::Implies(lhs, rhs) => {
                Tree::new("→".to_string()).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
            Formula::Until(lhs, int, rhs) => {
                Tree::new(format!("U{}", int)).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
            Formula::Release(lhs, int, rhs) => {
                Tree::new(format!("R{}", int)).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
            Formula::Globally(int, sub) => {
                Tree::new(format!("G{}", int)).with_leaves([sub.to_termtree()])
            }
            Formula::Finally(int, sub) => {
                Tree::new(format!("F{}", int)).with_leaves([sub.to_termtree()])
            }
            Formula::Next(time, sub) => {
                Tree::new(format!("X[{}]", time)).with_leaves([sub.to_termtree()])
            }
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_termtree())
    }
}

impl From<NNFFormula> for Formula {
    fn from(formula: NNFFormula) -> Self {
        match formula {
            NNFFormula::Literal(Literal::Atom(ap)) => Formula::AP(ap),
            NNFFormula::Literal(Literal::True) => Formula::True,
            NNFFormula::Literal(Literal::False) => Formula::False,

            NNFFormula::And(subs) => Formula::and(subs.into_iter().map(|f| f.into())),
            NNFFormula::Or(subs) => Formula::or(subs.into_iter().map(|f| f.into())),

            NNFFormula::Until(lhs, int, rhs) => Formula::Until(lhs.into(), int, rhs.into()),
            NNFFormula::Globally(int, sub) => Formula::Globally(int, sub.into()),
        }
    }
}

impl From<Box<NNFFormula>> for Box<Formula> {
    fn from(formula: Box<NNFFormula>) -> Self {
        Box::new(Formula::from(*formula))
    }
}
