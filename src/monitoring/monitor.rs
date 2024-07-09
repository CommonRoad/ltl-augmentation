use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    sets::interval::Interval,
    signals::{kleene::Kleene, signal::Signal},
};

use super::Logical;

pub trait TruthValue {
    fn top() -> Self;
    fn bottom() -> Self;
}

impl TruthValue for bool {
    fn top() -> Self {
        true
    }

    fn bottom() -> Self {
        false
    }
}

impl TruthValue for Kleene {
    fn top() -> Self {
        Kleene::True
    }

    fn bottom() -> Self {
        Kleene::False
    }
}

pub struct Monitor<T> {
    formula: NNFFormula<T>,
    atomic_propositions: HashSet<AtomicProposition>,
}

impl<T: Integer + Unsigned + Copy + SaturatingSub + Hash> Monitor<T> {
    pub fn new(formula: NNFFormula<T>) -> Self {
        let atomic_propositions = formula.collect_aps();
        Monitor {
            formula,
            atomic_propositions,
        }
    }

    pub fn monitor<V, Out>(&self, trace: &HashMap<&str, Signal<T, V>>) -> Out
    where
        V: TruthValue + Eq + Clone,
        Out: Logical<T> + From<Signal<T, V>>,
    {
        let missing_propositions = self
            .atomic_propositions
            .iter()
            .filter(|ap| !trace.contains_key(ap.name.as_ref()))
            .collect_vec();
        if !missing_propositions.is_empty() {
            panic!(
                "Missing atomic propositions in trace: {:?}",
                missing_propositions
            );
        }
        Monitor::monitor_rec(&self.formula, trace)
    }

    fn monitor_rec<V, Out>(formula: &NNFFormula<T>, trace: &HashMap<&str, Signal<T, V>>) -> Out
    where
        V: TruthValue + Eq + Clone,
        Out: Logical<T> + From<Signal<T, V>>,
    {
        match formula {
            NNFFormula::True => Signal::uniform(V::top()).into(),
            NNFFormula::False => Signal::uniform(V::bottom()).into(),
            NNFFormula::AP(ap) => {
                let signal = trace.get(ap.name.as_ref()).unwrap();
                if ap.negated {
                    Out::from(signal.clone()).negation()
                } else {
                    signal.clone().into()
                }
            }
            NNFFormula::And(subs) => subs
                .iter()
                .map(|sub| Monitor::monitor_rec(sub, trace))
                .reduce(|acc: Out, e| acc.conjunction(&e))
                .unwrap_or_else(|| Signal::uniform(V::top()).into()),
            NNFFormula::Or(subs) => subs
                .iter()
                .map(|sub| Monitor::monitor_rec(sub, trace))
                .reduce(|acc: Out, e| acc.disjunction(&e))
                .unwrap_or_else(|| Signal::uniform(V::bottom()).into()),
            NNFFormula::Until(lhs, interval, rhs) => {
                let lhs_signal: Out = Monitor::monitor_rec(lhs, trace);
                let rhs_signal = Monitor::monitor_rec(rhs, trace);
                lhs_signal.until(interval, &rhs_signal)
            }
            NNFFormula::Release(lhs, interval, rhs) => {
                let lhs_signal: Out = Monitor::monitor_rec(lhs, trace);
                let rhs_signal = Monitor::monitor_rec(rhs, trace);
                lhs_signal.release(interval, &rhs_signal)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{parser::mltl_parser, signals::kleene::KleeneSignal};

    use super::*;

    #[test]
    fn test_monitor_boolean() {
        let phi = mltl_parser::formula("a U[2, 5] b | c")
            .expect("Syntax is correct")
            .into();
        let monitor = Monitor::new(phi);

        let a_signal = Signal::from_positive_intervals(&[Interval::bounded(2_u32, 4)]);
        let b_signal = Signal::from_positive_intervals(&[Interval::bounded(5, 7)]);
        let c_signal = Signal::from_positive_intervals(&[Interval::bounded(10, 12)]);
        let trace = HashMap::from_iter([("a", a_signal), ("b", b_signal), ("c", c_signal)]);

        let expected = Signal::from_positive_intervals(&[
            Interval::bounded(0_u32, 5),
            Interval::bounded(8, 10),
        ]);

        let actual: Signal<_, bool> = monitor.monitor(&trace);

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_monitor_kleene() {
        let phi = mltl_parser::formula("a U[2, 5] b | c")
            .expect("Syntax is correct")
            .into();
        let monitor = Monitor::new(phi);

        let a_signal =
            Signal::indicator(Interval::bounded(2_u32, 4), Kleene::True, Kleene::Unknown);
        let b_signal = Signal::indicator(Interval::bounded(5, 7), Kleene::True, Kleene::False);
        let c_signal = Signal::indicator(Interval::bounded(10, 12), Kleene::True, Kleene::Unknown);
        let trace = HashMap::from_iter([("a", a_signal), ("b", b_signal), ("c", c_signal)]);

        let mut expected =
            Signal::indicator(Interval::bounded(0_u32, 5), Kleene::True, Kleene::Unknown);
        expected.set(&Interval::bounded(8, 10), Kleene::True);

        let actual: KleeneSignal<_> = monitor.monitor(&trace);
        dbg!(&actual);

        assert_eq!(Signal::from(actual), expected);
    }
}
