use std::{collections::HashMap, hash::Hash};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::NNFFormula,
    signals::{signal::Signal, truth_values::TruthValue},
    trace::Trace,
};

use super::Logical;

pub struct Monitor<'a, T, V> {
    root: &'a NNFFormula<T>,
    satisfaction_signals: HashMap<&'a NNFFormula<T>, Signal<T, V>>,
}

impl<'a, T, V> Monitor<'a, T, V> {
    pub fn root(&self) -> &'a NNFFormula<T> {
        self.root
    }

    pub fn satisfaction_signals(&self) -> &HashMap<&'a NNFFormula<T>, Signal<T, V>> {
        &self.satisfaction_signals
    }
}

impl<'a, T: Integer + Unsigned + Copy + SaturatingSub + Hash, V: TruthValue + Eq + Clone>
    Monitor<'a, T, V>
{
    pub fn new<L>(formula: &'a NNFFormula<T>, trace: &Trace<T, V>) -> Self
    where
        L: Logical<T> + From<Signal<T, V>> + Into<Signal<T, V>>,
    {
        let atomic_propositions = formula.collect_aps();
        let missing_propositions = atomic_propositions
            .iter()
            .filter(|ap| trace.get_ap_signal(ap.name.as_ref()).is_none())
            .collect_vec();
        if !missing_propositions.is_empty() {
            panic!(
                "Missing atomic propositions in trace: {:?}",
                missing_propositions
            );
        }
        let mut logical_signals = HashMap::new();
        Self::compute_satisfaction_signals::<L>(formula, trace, &mut logical_signals);
        let satisfaction_signals = logical_signals
            .into_iter()
            .map(|(formula, logical)| (formula, logical.into()))
            .collect();
        Monitor {
            root: formula,
            satisfaction_signals,
        }
    }

    fn compute_satisfaction_signals<L>(
        formula: &'a NNFFormula<T>,
        trace: &Trace<T, V>,
        logicals: &mut HashMap<&'a NNFFormula<T>, L>,
    ) where
        L: Logical<T> + From<Signal<T, V>> + Into<Signal<T, V>>,
    {
        if logicals.contains_key(formula) {
            return;
        }
        let logical_signal = match formula {
            NNFFormula::True => Signal::uniform(V::top()).into(),
            NNFFormula::False => Signal::uniform(V::bot()).into(),
            NNFFormula::AP(ap) => {
                let signal = trace.get_ap_signal(ap.name.as_ref()).unwrap();
                if ap.negated {
                    L::from(signal.clone()).negation()
                } else {
                    signal.clone().into()
                }
            }
            NNFFormula::And(subs) | NNFFormula::Or(subs) => {
                subs.iter()
                    .for_each(|sub| Self::compute_satisfaction_signals(sub, trace, logicals));
                let it = subs.iter().map(|sub| logicals.get(sub).unwrap());
                if matches!(formula, NNFFormula::And(..)) {
                    it.fold(L::from(Signal::uniform(V::top())), |acc, sig| {
                        acc.conjunction(sig)
                    })
                } else {
                    it.fold(L::from(Signal::uniform(V::bot())), |acc, sig| {
                        acc.disjunction(sig)
                    })
                }
            }
            NNFFormula::Until(lhs, interval, rhs) | NNFFormula::Release(lhs, interval, rhs) => {
                Self::compute_satisfaction_signals(lhs, trace, logicals);
                Self::compute_satisfaction_signals(rhs, trace, logicals);
                let lhs_signal = logicals.get(lhs.as_ref()).unwrap();
                let rhs_signal = logicals.get(rhs.as_ref()).unwrap();
                if matches!(formula, NNFFormula::Until(..)) {
                    lhs_signal.until(interval, rhs_signal)
                } else {
                    lhs_signal.release(interval, rhs_signal)
                }
            }
        };
        logicals.insert(formula, logical_signal);
    }
}

#[cfg(test)]
mod tests {
    use rstest::*;

    use crate::{
        monitoring::{boolean::BooleanMonitorSignal, kleene::KleeneMonitorSignal},
        parser::mltl_parser,
        sets::interval::Interval,
        signals::{boolean::BooleanSignal, truth_values::Kleene},
    };

    use super::*;

    #[fixture]
    fn phi() -> NNFFormula<u32> {
        mltl_parser::formula("a U[2, 5] b | c")
            .expect("Syntax is correct")
            .into()
    }

    #[rstest]
    fn test_monitor_boolean(phi: NNFFormula<u32>) {
        let a_signal = BooleanSignal::from_positive_intervals([Interval::bounded(2_u32, 4)]);
        let b_signal = BooleanSignal::from_positive_intervals([Interval::bounded(5, 7)]);
        let c_signal = BooleanSignal::from_positive_intervals([Interval::bounded(10, 12)]);
        let trace = Trace::from(HashMap::from_iter([
            ("a", a_signal),
            ("b", b_signal),
            ("c", c_signal),
        ]));

        let monitor = Monitor::new::<BooleanMonitorSignal<_>>(&phi, &trace);

        let expected = BooleanSignal::from_positive_intervals([
            Interval::bounded(0_u32, 5),
            Interval::bounded(8, 10),
        ]);

        let actual = monitor.satisfaction_signals().get(monitor.root()).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let expected = BooleanSignal::from_positive_intervals([
                Interval::bounded(5, 7),
                Interval::bounded(10, 12),
            ]);

            let actual = monitor.satisfaction_signals().get(rhs.as_ref()).unwrap();

            assert_eq!(actual, &expected);
        } else {
            unreachable!()
        }
    }

    #[rstest]
    fn test_monitor_kleene(phi: NNFFormula<u32>) {
        let a_signal =
            Signal::indicator(&Interval::bounded(2_u32, 4), Kleene::True, Kleene::Unknown);
        let b_signal = Signal::indicator(&Interval::bounded(5, 7), Kleene::True, Kleene::False);
        let c_signal = Signal::indicator(&Interval::bounded(10, 12), Kleene::True, Kleene::Unknown);
        let trace = Trace::from(HashMap::from_iter([
            ("a", a_signal),
            ("b", b_signal),
            ("c", c_signal),
        ]));

        let monitor = Monitor::new::<KleeneMonitorSignal<_>>(&phi, &trace);

        let mut expected =
            Signal::indicator(&Interval::bounded(0_u32, 5), Kleene::True, Kleene::Unknown);
        expected.set(&Interval::bounded(8, 10), Kleene::True);

        let actual = monitor.satisfaction_signals().get(monitor.root()).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let mut expected =
                Signal::indicator(&Interval::bounded(5, 7), Kleene::True, Kleene::Unknown);
            expected.set(&Interval::bounded(10, 12), Kleene::True);

            let actual = monitor.satisfaction_signals().get(rhs.as_ref()).unwrap();

            assert_eq!(actual, &expected);
        } else {
            unreachable!()
        }
    }
}
