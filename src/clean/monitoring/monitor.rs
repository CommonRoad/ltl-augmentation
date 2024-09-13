use std::collections::HashMap;

use super::Logical;
use crate::clean::formula::literal::Literal;
use crate::clean::formula::nnf::NNFFormula;
use crate::clean::{
    sequence::{NormalizedSequence, Sequence},
    trace::Trace,
    truth_values::TruthValue,
};

pub struct Monitor<V> {
    trace: Trace<V>,
    default: Option<V>,
}

impl<V: TruthValue + Eq + Clone> Monitor<V> {
    pub fn new(trace: Trace<V>) -> Self {
        Monitor {
            trace,
            default: None,
        }
    }

    pub fn with_default(trace: Trace<V>, default: V) -> Self {
        Monitor {
            trace,
            default: Some(default),
        }
    }

    pub fn evaluate<'a, L>(
        &self,
        formula: &'a NNFFormula,
    ) -> HashMap<&'a NNFFormula, NormalizedSequence<V>>
    where
        L: Logical + From<NormalizedSequence<V>> + Into<NormalizedSequence<V>>,
    {
        let mut logical_signals = HashMap::new();
        self.compute_satisfaction_signals::<L>(formula, &mut logical_signals);

        logical_signals
            .into_iter()
            .map(|(formula, logical)| (formula, logical.into()))
            .collect()
    }

    fn compute_satisfaction_signals<'a, L>(
        &self,
        formula: &'a NNFFormula,
        logicals: &mut HashMap<&'a NNFFormula, L>,
    ) where
        L: Logical + From<NormalizedSequence<V>> + Into<NormalizedSequence<V>>,
    {
        if logicals.contains_key(formula) {
            return;
        }
        let logical_signal = match formula {
            NNFFormula::Literal(Literal::True) => NormalizedSequence::uniform(V::top()).into(),
            NNFFormula::Literal(Literal::False) => NormalizedSequence::uniform(V::bot()).into(),
            NNFFormula::Literal(Literal::Atom(ap)) => {
                match self.trace.get_ap_sequence(ap.name.as_ref()) {
                    Some(sequence) => {
                        if ap.negated {
                            L::from(sequence.clone()).negation()
                        } else {
                            sequence.clone().into()
                        }
                    }
                    None => {
                        if let Some(default) = &self.default {
                            if ap.negated {
                                L::from(NormalizedSequence::uniform(default.clone())).negation()
                            } else {
                                NormalizedSequence::uniform(default.clone()).into()
                            }
                        } else {
                            panic!("Missing trace value for atomic proposition {}, but no default specified!", ap.name)
                        }
                    }
                }
            }
            NNFFormula::And(subs) | NNFFormula::Or(subs) => {
                subs.iter()
                    .for_each(|sub| self.compute_satisfaction_signals(sub, logicals));
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
                self.compute_satisfaction_signals(lhs, logicals);
                self.compute_satisfaction_signals(rhs, logicals);
                let lhs_signal = logicals.get(lhs.as_ref()).unwrap();
                let rhs_signal = logicals.get(rhs.as_ref()).unwrap();
                lhs_signal.until(interval, rhs_signal)
            }
            NNFFormula::Globally(interval, sub) => {
                self.compute_satisfaction_signals(sub, logicals);
                let sub_signal = logicals.get(sub.as_ref()).unwrap();
                sub_signal.globally(interval)
            }
        };
        logicals.insert(formula, logical_signal);
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use rstest::*;

    use super::*;
    use crate::clean::formula::parser::mltl_parser;
    use crate::clean::{
        monitoring::{boolean::BooleanMonitorSequence, kleene::KleeneMonitorSequence},
        sequence::boolean::BooleanSequence,
        sets::interval::Interval,
        truth_values::Kleene,
    };

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
            (Arc::from("a"), a_signal),
            (Arc::from("b"), b_signal),
            (Arc::from("c"), c_signal),
        ]));

        let monitor = Monitor::new(trace);

        let expected = BooleanSequence::from_positive_intervals([
            Interval::bounded(0_u32, 5),
            Interval::bounded(8, 10),
        ]);

        let satisfaction_sequences = monitor.evaluate::<BooleanMonitorSequence>(&phi);
        let actual = satisfaction_sequences.get(&phi).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let expected = BooleanSequence::from_positive_intervals([
                Interval::bounded(5, 7),
                Interval::bounded(10, 12),
            ]);

            let actual = satisfaction_sequences.get(rhs.as_ref()).unwrap();

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
            (Arc::from("a"), a_signal),
            (Arc::from("b"), b_signal),
            (Arc::from("c"), c_signal),
        ]));

        let monitor = Monitor::new(trace);

        let mut expected = NormalizedSequence::indicator(
            &Interval::bounded(0_u32, 5),
            Kleene::True,
            Kleene::Unknown,
        );
        expected.set(&Interval::bounded(8, 10), Kleene::True);

        let satisfaction_sequences = monitor.evaluate::<KleeneMonitorSequence>(&phi);
        let actual = satisfaction_sequences.get(&phi).unwrap();

        assert_eq!(actual, &expected);

        if let NNFFormula::Until(.., rhs) = &phi {
            let mut expected = NormalizedSequence::indicator(
                &Interval::bounded(5, 7),
                Kleene::True,
                Kleene::Unknown,
            );
            expected.set(&Interval::bounded(10, 12), Kleene::True);

            let actual = satisfaction_sequences.get(rhs.as_ref()).unwrap();

            assert_eq!(actual, &expected);
        } else {
            unreachable!()
        }
    }
}
