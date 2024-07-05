use std::collections::BTreeSet;

use itertools::Itertools;

use crate::interval::Interval;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Formula {
    // atomic proposition + constants
    AP(String),
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
}

impl Formula {
    pub fn negated(sub: Formula) -> Formula {
        Formula::Not(Box::new(sub))
    }

    pub fn and(subs: impl IntoIterator<Item = Formula>) -> Formula {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => Formula::True,
            1 => subs.pop_first().expect("Length is 1"),
            _ => Formula::And(subs),
        }
    }

    pub fn or(subs: impl IntoIterator<Item = Formula>) -> Formula {
        let mut subs: BTreeSet<_> = subs.into_iter().collect();
        match subs.len() {
            0 => Formula::False,
            1 => subs.pop_first().expect("Length is 1"),
            _ => Formula::Or(subs),
        }
    }

    pub fn implies(lhs: Formula, rhs: Formula) -> Formula {
        Formula::Implies(Box::new(lhs), Box::new(rhs))
    }

    pub fn until(lhs: Formula, int: Interval, rhs: Formula) -> Formula {
        Formula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn release(lhs: Formula, int: Interval, rhs: Formula) -> Formula {
        Formula::Release(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn globally(int: Interval, sub: Formula) -> Formula {
        Formula::Globally(int, Box::new(sub))
    }

    pub fn finally(int: Interval, sub: Formula) -> Formula {
        Formula::Finally(int, Box::new(sub))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNFFormula {
    // atomic proposition + constants
    AP(String, bool),
    True,
    False,

    // propositional connectives
    And(BTreeSet<NNFFormula>),
    Or(BTreeSet<NNFFormula>),

    // temporal connectives
    Until(Box<NNFFormula>, Interval, Box<NNFFormula>),
    Release(Box<NNFFormula>, Interval, Box<NNFFormula>),
}

impl NNFFormula {
    pub fn negated(self) -> NNFFormula {
        match self {
            NNFFormula::AP(name, negated) => NNFFormula::AP(name, !negated),
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

    pub fn and(subs: impl IntoIterator<Item = NNFFormula>) -> NNFFormula {
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

    pub fn or(subs: impl IntoIterator<Item = NNFFormula>) -> NNFFormula {
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

    pub fn until(lhs: NNFFormula, int: Interval, rhs: NNFFormula) -> NNFFormula {
        NNFFormula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn release(lhs: NNFFormula, int: Interval, rhs: NNFFormula) -> NNFFormula {
        NNFFormula::Release(Box::new(lhs), int, Box::new(rhs))
    }
}

impl From<Formula> for NNFFormula {
    fn from(formula: Formula) -> NNFFormula {
        match formula {
            Formula::AP(name) => NNFFormula::AP(name, false),
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
                Formula::AP(name) => NNFFormula::AP(name, true),
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

impl From<Box<Formula>> for Box<NNFFormula> {
    fn from(formula: Box<Formula>) -> Box<NNFFormula> {
        Box::new(NNFFormula::from(*formula))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::interval::Interval;

    #[test]
    fn test_nnf_simple() {
        let formula = Formula::negated(Formula::until(
            Formula::AP("a".to_string()),
            Interval::Range(3, 5),
            Formula::negated(Formula::AP("b".to_string())),
        ));

        let nnf = NNFFormula::release(
            NNFFormula::AP("a".to_string(), true),
            Interval::Range(3, 5),
            NNFFormula::AP("b".to_string(), false),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }

    #[test]
    fn test_nnf_complex() {
        let formula = Formula::negated(Formula::release(
            Formula::implies(Formula::AP("a".to_string()), Formula::AP("c".to_string())),
            Interval::Range(3, 5),
            Formula::finally(
                Interval::Range(0, 7),
                Formula::negated(Formula::AP("b".to_string())),
            ),
        ));

        let nnf = NNFFormula::until(
            NNFFormula::and([
                NNFFormula::AP("a".to_string(), false),
                NNFFormula::AP("c".to_string(), true),
            ]),
            Interval::Range(3, 5),
            NNFFormula::release(
                NNFFormula::False,
                Interval::Range(0, 7),
                NNFFormula::AP("b".to_string(), false),
            ),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }
}
