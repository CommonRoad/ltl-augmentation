use std::collections::HashMap;

use itertools::Itertools;

use crate::clean::{
    formula::NNFFormula,
    sequence::{NormalizedSequence, Sequence},
    trace::Trace,
    truth_values::TruthValue,
};

use super::Logical;

pub struct Monitor<'a, V> {
    root: &'a NNFFormula,
    satisfaction_signals: HashMap<&'a NNFFormula, NormalizedSequence<V>>,
}

impl<'a, V> Monitor<'a, V> {
    pub fn root(&self) -> &'a NNFFormula {
        self.root
    }

    pub fn satisfaction_signals(&self) -> &HashMap<&'a NNFFormula, NormalizedSequence<V>> {
        &self.satisfaction_signals
    }
}

impl<'a, V: TruthValue + Eq + Clone> Monitor<'a, V> {
    pub fn new<L>(formula: &'a NNFFormula, trace: &Trace<V>) -> Self
    where
        L: Logical + From<NormalizedSequence<V>> + Into<NormalizedSequence<V>>,
    {
        let atomic_propositions = formula.collect_aps();
        let missing_propositions = atomic_propositions
            .iter()
            .filter(|ap| trace.get_ap_sequence(ap.name.as_ref()).is_none())
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
        formula: &'a NNFFormula,
        trace: &Trace<V>,
        logicals: &mut HashMap<&'a NNFFormula, L>,
    ) where
        L: Logical + From<NormalizedSequence<V>> + Into<NormalizedSequence<V>>,
    {
        if logicals.contains_key(formula) {
            return;
        }
        let logical_signal = match formula {
            NNFFormula::True => NormalizedSequence::uniform(V::top()).into(),
            NNFFormula::False => NormalizedSequence::uniform(V::bot()).into(),
            NNFFormula::AP(ap) => {
                let signal = trace.get_ap_sequence(ap.name.as_ref()).unwrap();
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
                    it.fold(
                        L::from(NormalizedSequence::uniform(V::top())),
                        |acc, sig| acc.conjunction(sig),
                    )
                } else {
                    it.fold(
                        L::from(NormalizedSequence::uniform(V::bot())),
                        |acc, sig| acc.disjunction(sig),
                    )
                }
            }
            NNFFormula::Until(lhs, interval, rhs) => {
                Self::compute_satisfaction_signals(lhs, trace, logicals);
                Self::compute_satisfaction_signals(rhs, trace, logicals);
                let lhs_signal = logicals.get(lhs.as_ref()).unwrap();
                let rhs_signal = logicals.get(rhs.as_ref()).unwrap();
                lhs_signal.until(interval, rhs_signal)
            }
            NNFFormula::Globally(interval, sub) => {
                Self::compute_satisfaction_signals(sub, trace, logicals);
                let sub_signal = logicals.get(sub.as_ref()).unwrap();
                sub_signal.globally(interval)
            }
        };
        logicals.insert(formula, logical_signal);
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use rstest::*;

    use crate::clean::{
        monitoring::{boolean::BooleanMonitorSequence, kleene::KleeneMonitorSequence},
        parser::mltl_parser,
        sequence::boolean::BooleanSequence,
        sets::interval::Interval,
        truth_values::Kleene,
    };

    use super::*;

    #[fixture]
    fn phi() -> NNFFormula {
        mltl_parser::formula("a U[2, 5] b | c")
            .expect("Syntax is correct")
            .into()
    }

    #[rstest]
    fn test_monitor_boolean(phi: NNFFormula) {
        let a_signal = BooleanSequence::from_positive_intervals([Interval::bounded(2_u32, 4)]);
        let b_signal = BooleanSequence::from_positive_intervals([Interval::bounded(5, 7)]);
        let c_signal = BooleanSequence::from_positive_intervals([Interval::bounded(10, 12)]);
        let trace = Trace::from(HashMap::from_iter([
            (Rc::from("a"), a_signal),
            (Rc::from("b"), b_signal),
            (Rc::from("c"), c_signal),
        ]));

        let monitor = Monitor::new::<BooleanMonitorSequence>(&phi, &trace);

        let expected = BooleanSequence::from_positive_intervals([
            Interval::bounded(0_u32, 5),
            Interval::bounded(8, 10),
        ]);

        let actual = monitor.satisfaction_signals().get(monitor.root()).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let expected = BooleanSequence::from_positive_intervals([
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
    fn test_monitor_kleene(phi: NNFFormula) {
        let a_signal = NormalizedSequence::indicator(
            &Interval::bounded(2_u32, 4),
            Kleene::True,
            Kleene::Unknown,
        );
        let b_signal =
            NormalizedSequence::indicator(&Interval::bounded(5, 7), Kleene::True, Kleene::False);
        let c_signal = NormalizedSequence::indicator(
            &Interval::bounded(10, 12),
            Kleene::True,
            Kleene::Unknown,
        );
        let trace = Trace::from(HashMap::from_iter([
            (Rc::from("a"), a_signal),
            (Rc::from("b"), b_signal),
            (Rc::from("c"), c_signal),
        ]));

        let monitor = Monitor::new::<KleeneMonitorSequence>(&phi, &trace);

        let mut expected = NormalizedSequence::indicator(
            &Interval::bounded(0_u32, 5),
            Kleene::True,
            Kleene::Unknown,
        );
        expected.set(&Interval::bounded(8, 10), Kleene::True);

        let actual = monitor.satisfaction_signals().get(monitor.root()).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let mut expected = NormalizedSequence::indicator(
                &Interval::bounded(5, 7),
                Kleene::True,
                Kleene::Unknown,
            );
            expected.set(&Interval::bounded(10, 12), Kleene::True);

            let actual = monitor.satisfaction_signals().get(rhs.as_ref()).unwrap();

            assert_eq!(actual, &expected);
        } else {
            unreachable!()
        }
    }
}
