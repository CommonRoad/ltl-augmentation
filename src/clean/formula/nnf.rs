use crate::clean::formula::atomic_proposition::AtomicProposition;
use crate::clean::formula::literal::Literal;
use crate::clean::formula::ltl::Formula;
use crate::clean::sequence::Time;
use crate::clean::sets::interval::Interval;
use crate::clean::sets::interval_set::IntervalSet;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Display;
use termtree::Tree;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNFFormula {
    // literals
    Literal(Literal),

    // propositional connectives
    And(BTreeSet<NNFFormula>),
    Or(BTreeSet<NNFFormula>),

    // temporal connectives
    Until(Box<NNFFormula>, Interval, Box<NNFFormula>),
    Globally(Interval, Box<NNFFormula>),
}

impl NNFFormula {
    pub fn is_literal(&self) -> bool {
        matches!(self, NNFFormula::Literal(..))
    }

    pub fn is_true(&self) -> bool {
        matches!(self, NNFFormula::Literal(Literal::True))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, NNFFormula::Literal(Literal::False))
    }

    pub fn is_next(&self) -> bool {
        matches!(self, NNFFormula::Globally(int, _) if int.is_singleton())
    }

    pub fn get_interval(&self) -> Interval {
        match self {
            NNFFormula::Literal(..) | NNFFormula::And(..) | NNFFormula::Or(..) => {
                Interval::singleton(0)
            }
            NNFFormula::Until(_, interval, _) | NNFFormula::Globally(interval, _) => *interval,
        }
    }

    pub fn iter_subformulas(&self) -> Box<dyn Iterator<Item = &NNFFormula> + '_> {
        match self {
            NNFFormula::Literal(..) => Box::new(std::iter::empty()),
            NNFFormula::And(subs) | NNFFormula::Or(subs) => Box::new(subs.iter()),
            NNFFormula::Until(lhs, _, rhs) => {
                Box::new(std::iter::once(lhs.as_ref()).chain(std::iter::once(rhs.as_ref())))
            }
            NNFFormula::Globally(_, sub) => Box::new(std::iter::once(sub.as_ref())),
        }
    }

    pub fn negated(self) -> Self {
        match self {
            NNFFormula::Literal(literal) => NNFFormula::Literal(literal.negated()),
            NNFFormula::And(subs) => NNFFormula::or(subs.into_iter().map(|f| f.negated())),
            NNFFormula::Or(subs) => NNFFormula::and(subs.into_iter().map(|f| f.negated())),
            NNFFormula::Until(lhs, int, rhs) => {
                NNFFormula::release(lhs.negated(), int, rhs.negated())
            }
            NNFFormula::Globally(int, sub) => NNFFormula::finally(int, sub.negated()),
        }
    }

    pub fn true_literal() -> Self {
        NNFFormula::Literal(Literal::True)
    }

    pub fn false_literal() -> Self {
        NNFFormula::Literal(Literal::False)
    }

    pub fn and(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs
            .into_iter()
            .filter(|f| !f.is_true())
            .flat_map(|f| match f {
                NNFFormula::And(subs) => subs,
                f => [f].into(),
            })
            .collect();
        match subs.len() {
            0 => NNFFormula::true_literal(),
            1 => subs.pop_first().expect("Length is 1"),
            _ if subs.iter().any(NNFFormula::is_false) => NNFFormula::false_literal(),
            _ => NNFFormula::And(subs),
        }
    }

    pub fn or(subs: impl IntoIterator<Item = Self>) -> Self {
        let mut subs: BTreeSet<_> = subs
            .into_iter()
            .filter(|f| !f.is_false())
            .flat_map(|f| match f {
                NNFFormula::Or(subs) => subs,
                f => [f].into(),
            })
            .collect();
        match subs.len() {
            0 => NNFFormula::false_literal(),
            1 => subs.pop_first().expect("Length is 1"),
            _ if subs.iter().any(NNFFormula::is_true) => NNFFormula::true_literal(),
            _ => NNFFormula::Or(subs),
        }
    }

    pub fn implies(lhs: Self, rhs: Self) -> Self {
        NNFFormula::or([lhs.negated(), rhs])
    }

    pub fn until(lhs: Self, int: Interval, rhs: Self) -> Self {
        if rhs.is_false() || int.is_empty() {
            return NNFFormula::false_literal();
        }
        if rhs.is_true() {
            // Due to MLTL semantics for U[a, b]: rhs always holds directly at a, so lhs is never required
            return NNFFormula::true_literal();
        }
        if lhs.is_false() || int.is_singleton() {
            return NNFFormula::next(*int.lb().expect("interval should not be empty"), rhs);
        }
        NNFFormula::Until(Box::new(lhs), int, Box::new(rhs))
    }

    pub fn globally(int: Interval, sub: Self) -> Self {
        if sub.is_true() || int.is_empty() {
            return NNFFormula::true_literal();
        }
        if sub.is_false() {
            return NNFFormula::false_literal();
        }
        if int == Interval::singleton(0) {
            return sub;
        }
        NNFFormula::Globally(int, Box::new(sub))
    }

    pub fn release(lhs: Self, int: Interval, rhs: Self) -> Self {
        if rhs.is_false() {
            // This requires false to hold in the current state, which is impossible
            return NNFFormula::false_literal();
        }
        if rhs.is_true() | int.is_empty() {
            // Due to MLTL semantics, rhs only needs to hold within the interval
            return NNFFormula::true_literal();
        }
        if lhs.is_true() || int.is_singleton() {
            return NNFFormula::next(*int.lb().expect("interval should not be empty"), rhs);
        }
        NNFFormula::or([
            NNFFormula::globally(int, rhs.clone()),
            NNFFormula::until(rhs.clone(), int, NNFFormula::and([lhs, rhs])),
        ])
    }

    pub fn finally(int: Interval, sub: Self) -> Self {
        NNFFormula::until(NNFFormula::true_literal(), int, sub)
    }

    pub fn next(time: Time, sub: Self) -> Self {
        if time == 0 {
            sub
        } else {
            NNFFormula::globally(Interval::singleton(time), sub)
        }
    }

    pub fn collect_aps(&self) -> HashSet<AtomicProposition> {
        match self {
            NNFFormula::Literal(Literal::True) | NNFFormula::Literal(Literal::False) => {
                HashSet::new()
            }
            NNFFormula::Literal(Literal::Atom(ap)) => HashSet::from([ap.clone()]),
            NNFFormula::And(subs) | NNFFormula::Or(subs) => subs
                .iter()
                .map(|f| f.collect_aps())
                .reduce(|mut acc, e| {
                    acc.extend(e);
                    acc
                })
                .unwrap_or_default(),
            NNFFormula::Until(lhs, _, rhs) => {
                let mut set = lhs.collect_aps();
                set.extend(rhs.collect_aps());
                set
            }
            NNFFormula::Globally(_, sub) => sub.collect_aps(),
        }
    }

    pub fn collect_aps_with_time(&self) -> HashMap<AtomicProposition, IntervalSet> {
        let mut aps = HashMap::new();
        self.collect_aps_with_time_rec(&Interval::singleton(0), &mut aps);
        aps
    }

    fn collect_aps_with_time_rec(
        &self,
        interval: &Interval,
        map: &mut HashMap<AtomicProposition, IntervalSet>,
    ) {
        match self {
            NNFFormula::Literal(Literal::True) | NNFFormula::Literal(Literal::False) => {}
            NNFFormula::Literal(Literal::Atom(ap)) => {
                map.entry(ap.clone()).or_default().add(interval);
            }
            NNFFormula::And(subs) | NNFFormula::Or(subs) => {
                subs.iter()
                    .for_each(|sub| sub.collect_aps_with_time_rec(interval, map));
            }
            NNFFormula::Until(lhs, int, rhs) => {
                let new_interval = interval.minkowski_sum(*int);
                lhs.collect_aps_with_time_rec(&new_interval, map);
                rhs.collect_aps_with_time_rec(&new_interval, map);
            }
            NNFFormula::Globally(int, sub) => {
                let new_interval = interval.minkowski_sum(*int);
                sub.collect_aps_with_time_rec(&new_interval, map);
            }
        }
    }
}

impl From<Formula> for NNFFormula {
    fn from(formula: Formula) -> Self {
        match formula {
            Formula::AP(ap) => NNFFormula::Literal(Literal::Atom(ap)),
            Formula::True => NNFFormula::true_literal(),
            Formula::False => NNFFormula::false_literal(),

            Formula::And(subs) => NNFFormula::and(subs.into_iter().map(|f| f.into())),
            Formula::Or(subs) => NNFFormula::or(subs.into_iter().map(|f| f.into())),
            Formula::Implies(lhs, rhs) => Formula::or([Formula::Not(lhs), *rhs]).into(),

            Formula::Until(lhs, int, rhs) => NNFFormula::until((*lhs).into(), int, (*rhs).into()),
            Formula::Release(lhs, int, rhs) => {
                NNFFormula::release((*lhs).into(), int, (*rhs).into())
            }

            Formula::Globally(int, sub) => NNFFormula::globally(int, (*sub).into()),
            Formula::Finally(int, sub) => NNFFormula::finally(int, (*sub).into()),
            Formula::Next(time, sub) => NNFFormula::next(time, (*sub).into()),

            Formula::Not(sub) => match *sub {
                Formula::AP(AtomicProposition { name, negated }) => {
                    NNFFormula::Literal(Literal::Atom(AtomicProposition {
                        name,
                        negated: !negated,
                    }))
                }
                Formula::True => NNFFormula::false_literal(),
                Formula::False => NNFFormula::true_literal(),

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
                Formula::Next(time, sub) => Formula::next(time, Formula::Not(sub)).into(),

                Formula::Not(sub) => (*sub).into(),
            },
        }
    }
}

impl From<Box<Formula>> for Box<NNFFormula> {
    fn from(formula: Box<Formula>) -> Self {
        Box::new(NNFFormula::from(*formula))
    }
}

impl NNFFormula {
    fn to_termtree(&self) -> Tree<String> {
        match self {
            NNFFormula::Literal(literal) => Tree::new(format!("{}", literal)),

            NNFFormula::And(subs) => {
                Tree::new("∧".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            NNFFormula::Or(subs) => {
                Tree::new("∨".to_string()).with_leaves(subs.iter().map(|f| f.to_termtree()))
            }
            NNFFormula::Until(lhs, int, rhs) if lhs.is_true() => {
                Tree::new(format!("F{}", int)).with_leaves([rhs.to_termtree()])
            }
            NNFFormula::Until(lhs, int, rhs) => {
                Tree::new(format!("U{}", int)).with_leaves([lhs.to_termtree(), rhs.to_termtree()])
            }
            NNFFormula::Globally(int, sub) => {
                Tree::new(format!("G{}", int)).with_leaves([sub.to_termtree()])
            }
        }
    }
}

impl Display for NNFFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_termtree())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::clean::formula::parser::mltl_parser;

    use super::*;

    #[test]
    fn test_nnf_simple() {
        let formula = mltl_parser::formula("!(a U[3, 5] !b)").expect("Syntax is correct");

        let nnf = NNFFormula::release(
            NNFFormula::Literal(Literal::Atom(AtomicProposition {
                name: Arc::from("a"),
                negated: true,
            })),
            Interval::bounded(3, 5),
            NNFFormula::Literal(Literal::Atom(AtomicProposition {
                name: Arc::from("b"),
                negated: false,
            })),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }

    #[test]
    fn test_nnf_complex() {
        let formula =
            mltl_parser::formula("!((a -> c) R[3, 5] (F[0, 7] !b))").expect("Syntax is correct");

        let nnf = NNFFormula::until(
            NNFFormula::and([
                NNFFormula::Literal(Literal::Atom(AtomicProposition {
                    name: Arc::from("a"),
                    negated: false,
                })),
                NNFFormula::Literal(Literal::Atom(AtomicProposition {
                    name: Arc::from("c"),
                    negated: true,
                })),
            ]),
            Interval::bounded(3, 5),
            NNFFormula::release(
                NNFFormula::false_literal(),
                Interval::bounded(0, 7),
                NNFFormula::Literal(Literal::Atom(AtomicProposition {
                    name: Arc::from("b"),
                    negated: false,
                })),
            ),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }
}
