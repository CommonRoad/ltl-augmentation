use std::{
    collections::{BTreeSet, HashSet},
    fmt::Display,
    hash::Hash,
    rc::Rc,
};

use itertools::Itertools;
use num::{Integer, Unsigned};
use termtree::Tree;

use crate::sets::interval::Interval;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AtomicProposition {
    pub name: Rc<str>,
    pub negated: bool,
}

impl Display for AtomicProposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.negated {
            write!(f, "¬{}", self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Formula<T> {
    // atomic proposition + constants
    AP(AtomicProposition),
    True,
    False,

    // propositional connectives
    Not(Box<Formula<T>>),
    And(BTreeSet<Formula<T>>),
    Or(BTreeSet<Formula<T>>),
    Implies(Box<Formula<T>>, Box<Formula<T>>),

    // temporal connectives
    Until(Box<Formula<T>>, Interval<T>, Box<Formula<T>>),
    Release(Box<Formula<T>>, Interval<T>, Box<Formula<T>>),
    Globally(Interval<T>, Box<Formula<T>>),
    Finally(Interval<T>, Box<Formula<T>>),
}

impl<T: Integer + Unsigned + Copy> Formula<T> {
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

    pub fn until(lhs: Self, int: Interval<T>, rhs: Self) -> Self {
        Formula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn release(lhs: Self, int: Interval<T>, rhs: Self) -> Self {
        Formula::Release(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn globally(int: Interval<T>, sub: Self) -> Self {
        Formula::Globally(int, Box::new(sub))
    }

    pub fn finally(int: Interval<T>, sub: Self) -> Self {
        Formula::Finally(int, Box::new(sub))
    }
}

impl<T: Display> Formula<T> {
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
        }
    }
}

impl<T: Display> Display for Formula<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_termtree())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNFFormula<T> {
    // atomic proposition + constants
    AP(AtomicProposition),
    True,
    False,

    // propositional connectives
    And(BTreeSet<NNFFormula<T>>),
    Or(BTreeSet<NNFFormula<T>>),

    // temporal connectives
    Until(Box<NNFFormula<T>>, Interval<T>, Box<NNFFormula<T>>),
    Release(Box<NNFFormula<T>>, Interval<T>, Box<NNFFormula<T>>),
}

impl<T: Integer + Unsigned + Copy + Hash> NNFFormula<T> {
    pub fn negated(self) -> Self {
        match self {
            NNFFormula::AP(AtomicProposition { name, negated }) => {
                NNFFormula::AP(AtomicProposition {
                    name,
                    negated: !negated,
                })
            }
            NNFFormula::True => NNFFormula::False,
            NNFFormula::False => NNFFormula::True,
            NNFFormula::And(subs) => NNFFormula::or(subs.into_iter().map(|f| f.negated())),
            NNFFormula::Or(subs) => NNFFormula::and(subs.into_iter().map(|f| f.negated())),
            NNFFormula::Until(lhs, int, rhs) => {
                NNFFormula::release(lhs.negated(), int, rhs.negated())
            }
            NNFFormula::Release(lhs, int, rhs) => {
                NNFFormula::until(lhs.negated(), int, rhs.negated())
            }
        }
    }

    pub fn is_negation_of(&self, other: &Self) -> bool {
        match (self, other) {
            (NNFFormula::AP(ap1), NNFFormula::AP(ap2)) if ap1.name == ap2.name => {
                ap1.negated != ap2.negated
            }
            (NNFFormula::True, NNFFormula::False) | (NNFFormula::False, NNFFormula::True) => true,
            (NNFFormula::And(subs1), NNFFormula::Or(subs2))
            | (NNFFormula::Or(subs1), NNFFormula::And(subs2))
                if subs1.len() == subs2.len() =>
            {
                subs1
                    .iter()
                    .all(|f1| subs2.iter().any(|f2| f1.is_negation_of(f2)))
            }
            (NNFFormula::Until(lhs1, int1, rhs1), NNFFormula::Release(lhs2, int2, rhs2))
            | (NNFFormula::Release(lhs1, int1, rhs1), NNFFormula::Until(lhs2, int2, rhs2))
                if int1 == int2 =>
            {
                lhs1.is_negation_of(lhs2) && rhs1.is_negation_of(rhs2)
            }
            _ => false,
        }
    }

    pub fn and(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => NNFFormula::True,
            1 => subs.pop_first().expect("Length is 1"),
            _ if subs.iter().any(|f| matches!(f, NNFFormula::False)) => NNFFormula::False,
            _ => NNFFormula::And(
                subs.into_iter()
                    .filter(|f| !matches!(f, NNFFormula::True))
                    .flat_map(|f| match f {
                        NNFFormula::And(subs) => subs,
                        f => [f].into(),
                    })
                    .unique()
                    .collect(),
            ),
        }
    }

    pub fn or(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => NNFFormula::False,
            1 => subs.pop_first().expect("Length is 1"),
            _ if subs.iter().any(|f| matches!(f, NNFFormula::True)) => NNFFormula::True,
            _ => NNFFormula::Or(
                subs.into_iter()
                    .filter(|f| !matches!(f, NNFFormula::False))
                    .flat_map(|f| match f {
                        NNFFormula::Or(subs) => subs,
                        f => [f].into(),
                    })
                    .unique()
                    .collect(),
            ),
        }
    }

    pub fn until(lhs: Self, int: Interval<T>, rhs: Self) -> Self {
        if matches!(rhs, NNFFormula::False) || int.is_empty() {
            return NNFFormula::False;
        }
        if matches!(rhs, NNFFormula::True) {
            // Due to MLTL semantics for U[a, b]: rhs always holds directly at a, so lhs is never required
            return NNFFormula::True;
        }
        if matches!(lhs, NNFFormula::False) || int.is_singleton() {
            return NNFFormula::next(*int.lb().expect("interval should not be empty"), rhs);
        }
        NNFFormula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn release(lhs: Self, int: Interval<T>, rhs: Self) -> Self {
        if matches!(rhs, NNFFormula::False) {
            // This requires false to hold in the current state, which is impossible
            return NNFFormula::False;
        }
        if matches!(rhs, NNFFormula::True) | int.is_empty() {
            // Due to MLTL semantics, rhs only needs to hold within the interval
            return NNFFormula::True;
        }
        if matches!(lhs, NNFFormula::True) {
            return NNFFormula::next(*int.lb().expect("interval should not be empty"), rhs);
        }
        if int.is_singleton() {
            return NNFFormula::Release(Box::new(NNFFormula::False), int, Box::new(rhs));
        }
        NNFFormula::Release(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn finally(int: Interval<T>, sub: Self) -> Self {
        NNFFormula::until(NNFFormula::True, int, sub)
    }

    pub fn globally(int: Interval<T>, sub: Self) -> Self {
        NNFFormula::release(NNFFormula::False, int, sub)
    }

    pub fn next(time: T, sub: Self) -> Self {
        NNFFormula::globally(Interval::singleton(time), sub)
    }

    pub fn collect_aps(&self) -> HashSet<AtomicProposition> {
        match self {
            NNFFormula::True | NNFFormula::False => HashSet::new(),
            NNFFormula::AP(ap) => HashSet::from([ap.clone()]),
            NNFFormula::And(subs) | NNFFormula::Or(subs) => subs
                .iter()
                .map(|f| f.collect_aps())
                .reduce(|mut acc, e| {
                    acc.extend(e);
                    acc
                })
                .unwrap_or_default(),
            NNFFormula::Until(lhs, _, rhs) | NNFFormula::Release(lhs, _, rhs) => {
                let mut set = lhs.collect_aps();
                set.extend(rhs.collect_aps());
                set
            }
        }
    }
}

impl<T: Integer + Unsigned + Copy + Hash> From<Formula<T>> for NNFFormula<T> {
    fn from(formula: Formula<T>) -> Self {
        match formula {
            Formula::AP(ap) => NNFFormula::AP(ap),
            Formula::True => NNFFormula::True,
            Formula::False => NNFFormula::False,

            Formula::And(subs) => NNFFormula::and(subs.into_iter().map(|f| f.into())),
            Formula::Or(subs) => NNFFormula::or(subs.into_iter().map(|f| f.into())),
            Formula::Implies(lhs, rhs) => Formula::or([Formula::Not(lhs), *rhs]).into(),

            Formula::Until(lhs, int, rhs) => NNFFormula::Until(lhs.into(), int, rhs.into()),
            Formula::Release(lhs, int, rhs) => NNFFormula::Release(lhs.into(), int, rhs.into()),

            Formula::Globally(int, sub) => {
                NNFFormula::Release(Box::new(NNFFormula::False), int, sub.into())
            }
            Formula::Finally(int, sub) => {
                NNFFormula::Until(Box::new(NNFFormula::True), int, sub.into())
            }

            Formula::Not(sub) => match *sub {
                Formula::AP(AtomicProposition { name, negated }) => {
                    NNFFormula::AP(AtomicProposition {
                        name,
                        negated: !negated,
                    })
                }
                Formula::True => NNFFormula::False,
                Formula::False => NNFFormula::True,

                Formula::And(subs) => {
                    NNFFormula::or(subs.into_iter().map(|f| Formula::negated(f).into()))
                }
                Formula::Or(subs) => {
                    NNFFormula::and(subs.into_iter().map(|f| Formula::negated(f).into()))
                }
                Formula::Implies(lhs, rhs) => Formula::and([*lhs, Formula::Not(rhs)]).into(),

                Formula::Until(lhs, int, rhs) => {
                    NNFFormula::release(Formula::Not(lhs).into(), int, Formula::Not(rhs).into())
                }
                Formula::Release(lhs, int, rhs) => {
                    NNFFormula::until(Formula::Not(lhs).into(), int, Formula::Not(rhs).into())
                }

                Formula::Globally(int, sub) => Formula::finally(int, Formula::Not(sub)).into(),
                Formula::Finally(int, sub) => Formula::globally(int, Formula::Not(sub)).into(),

                Formula::Not(sub) => (*sub).into(),
            },
        }
    }
}

impl<T: Integer + Unsigned + Copy + Hash> From<Box<Formula<T>>> for Box<NNFFormula<T>> {
    fn from(formula: Box<Formula<T>>) -> Self {
        Box::new(NNFFormula::from(*formula))
    }
}

impl<T: Display + PartialEq> NNFFormula<T> {
    fn to_termtree(&self) -> Tree<String> {
        match self {
            NNFFormula::AP(ap) => Tree::new(format!("{}", ap)),
            NNFFormula::True => Tree::new("⊤".to_string()),
            NNFFormula::False => Tree::new("⊥".to_string()),

            NNFFormula::And(subs) => {
                Tree::new("∧".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            NNFFormula::Or(subs) => {
                Tree::new("∨".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            NNFFormula::Until(lhs, int, rhs) if **lhs == NNFFormula::True => {
                let op = if matches!(int, Interval::Bounded { lb, ub } if lb == ub) {
                    "X"
                } else {
                    "F"
                };
                Tree::new(format!("{}{}", op, int)).with_leaves([rhs.to_termtree()])
            }
            NNFFormula::Release(lhs, int, rhs) if **lhs == NNFFormula::False => {
                let op = if matches!(int, Interval::Bounded { lb, ub } if lb == ub) {
                    "X"
                } else {
                    "G"
                };
                Tree::new(format!("{}{}", op, int)).with_leaves([rhs.to_termtree()])
            }
            NNFFormula::Until(lhs, int, rhs) => {
                Tree::new(format!("U{}", int)).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
            NNFFormula::Release(lhs, int, rhs) => {
                Tree::new(format!("R{}", int)).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
        }
    }
}

impl<T: Display + Integer + Unsigned + Copy> Display for NNFFormula<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_termtree())
    }
}

impl<T: Integer + Unsigned + Copy> From<NNFFormula<T>> for Formula<T> {
    fn from(formula: NNFFormula<T>) -> Self {
        match formula {
            NNFFormula::AP(ap) => Formula::AP(ap),
            NNFFormula::True => Formula::True,
            NNFFormula::False => Formula::False,

            NNFFormula::And(subs) => Formula::and(subs.into_iter().map(|f| f.into())),
            NNFFormula::Or(subs) => Formula::or(subs.into_iter().map(|f| f.into())),

            NNFFormula::Until(lhs, int, rhs) => Formula::Until(lhs.into(), int, rhs.into()),
            NNFFormula::Release(lhs, int, rhs) => Formula::Release(lhs.into(), int, rhs.into()),
        }
    }
}

impl<T: Integer + Unsigned + Copy> From<Box<NNFFormula<T>>> for Box<Formula<T>> {
    fn from(formula: Box<NNFFormula<T>>) -> Self {
        Box::new(Formula::from(*formula))
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::mltl_parser;

    use super::*;

    #[test]
    fn test_nnf_simple() {
        let formula = mltl_parser::formula("!(a U[3, 5] !b)").expect("Syntax is correct");

        let nnf = NNFFormula::release(
            NNFFormula::AP(AtomicProposition {
                name: Rc::from("a"),
                negated: true,
            }),
            Interval::bounded(3, 5),
            NNFFormula::AP(AtomicProposition {
                name: Rc::from("b"),
                negated: false,
            }),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }

    #[test]
    fn test_nnf_complex() {
        let formula =
            mltl_parser::formula("!((a -> c) R[3, 5] (F[0, 7] !b))").expect("Syntax is correct");

        let nnf = NNFFormula::until(
            NNFFormula::and([
                NNFFormula::AP(AtomicProposition {
                    name: Rc::from("a"),
                    negated: false,
                }),
                NNFFormula::AP(AtomicProposition {
                    name: Rc::from("c"),
                    negated: true,
                }),
            ]),
            Interval::bounded(3, 5),
            NNFFormula::release(
                NNFFormula::False,
                Interval::bounded(0, 7),
                NNFFormula::AP(AtomicProposition {
                    name: Rc::from("b"),
                    negated: false,
                }),
            ),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }
}
