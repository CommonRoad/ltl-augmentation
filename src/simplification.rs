use std::{collections::HashMap, hash::Hash};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    monitoring::{kleene::KleeneMonitorSignal, monitor::Monitor},
    sets::interval::Interval,
    signals::{signal::Signal, truth_values::Kleene},
    trace::Trace,
};

type FormulaSignal<T> = Signal<T, NNFFormula<T>>;

pub struct Simplifier<'a, T> {
    root: &'a NNFFormula<T>,
    knowledge: Monitor<'a, T, Kleene>,
    simplification_signals: HashMap<&'a NNFFormula<T>, FormulaSignal<T>>,
}

impl<'a, T: Integer + Unsigned + Copy + SaturatingSub + Hash> Simplifier<'a, T> {
    pub fn new(formula: &'a NNFFormula<T>, trace: &'a Trace<T, Kleene>) -> Self {
        let knowledge = Monitor::new::<KleeneMonitorSignal<_>>(formula, trace);
        Simplifier {
            root: formula,
            knowledge,
            simplification_signals: HashMap::new(),
        }
    }

    pub fn simplify(&mut self) {
        self.simplify_rec(self.root, &Interval::singleton(T::zero()))
    }

    fn simplify_rec(&mut self, formula: &'a NNFFormula<T>, interval: &Interval<T>) {
        let simplification_signal = match formula {
            NNFFormula::True | NNFFormula::False => Signal::uniform(formula.clone()),
            NNFFormula::AP(_) => self
                .knowledge
                .satisfaction_signals()
                .get(&formula)
                .map(|ap_trace| {
                    ap_trace.map(|kleene_val| match kleene_val {
                        Kleene::True => NNFFormula::True,
                        Kleene::False => NNFFormula::False,
                        Kleene::Unknown => formula.clone(),
                    })
                })
                .unwrap_or_else(|| Signal::uniform(formula.clone())),
            NNFFormula::And(subs) | NNFFormula::Or(subs) => {
                subs.iter().for_each(|sub| self.simplify_rec(sub, interval));
                let it = subs
                    .iter()
                    .map(|sub| self.simplification_signals.get(sub).unwrap());
                if matches!(formula, NNFFormula::And(..)) {
                    it.fold(Signal::uniform(NNFFormula::True), |acc, sig| {
                        acc.combine(sig, |f1, f2| NNFFormula::and([f1.clone(), f2.clone()]))
                    })
                } else {
                    it.fold(Signal::uniform(NNFFormula::False), |acc, sig| {
                        acc.combine(sig, |f1, f2| NNFFormula::or([f1.clone(), f2.clone()]))
                    })
                }
            }
            NNFFormula::Until(lhs, int, rhs) => {
                let lhs_simp = self.simplification_signals.get(lhs.as_ref()).unwrap();
                let rhs_simp = self.simplification_signals.get(rhs.as_ref()).unwrap();
                let split = lhs_simp.combine(rhs_simp, |f1, f2| (f1.clone(), f2.clone()));

                let unknown_intervals = self
                    .knowledge
                    .satisfaction_signals()
                    .get(formula)
                    .expect("knowledge should contain all subformulas")
                    .intervals_where_eq(&Kleene::Unknown)
                    .into_iter()
                    .map(|i| i.intersect(int))
                    .filter(|i| !i.is_empty())
                    .collect_vec();
                let relevant_intervals_subs = unknown_intervals
                    .into_iter()
                    .map(|i| i + *int)
                    .collect_vec();
                todo!()
            }
            _ => todo!(),
        };
        self.simplification_signals
            .insert(formula, simplification_signal);
    }

    fn get_until_simplification(
        unknown_interval: &Interval<u32>,
        lhs_simp: &FormulaSignal<u32>,
        until_interval: &Interval<u32>,
        rhs_simp: &FormulaSignal<u32>,
    ) -> FormulaSignal<u32> {
        let last_change = lhs_simp.last_change().max(rhs_simp.last_change());
        let mut simp_signal = Signal::uniform(NNFFormula::False);
        for t in interval_iter(unknown_interval) {
            let omega = *until_interval + Interval::singleton(t);
            let splits = lhs_simp.get_refined_intervals_in(rhs_simp, &omega);
            let mut disjunction = NNFFormula::False;
            for split in splits {
                let x = *split.lb().expect("split should not be empty");
                let until = NNFFormula::until(
                    lhs_simp.at(x).clone(),
                    split - Interval::singleton(t),
                    rhs_simp.at(x).clone(),
                );
                if matches!(until, NNFFormula::False) {
                    continue;
                }
                if x < 1 {
                    disjunction = NNFFormula::or([disjunction, until]);
                    continue;
                }
                // [t + a, x - 1]
                let globally_interval = until_interval
                    .minkowski_sum(Interval::singleton(t))
                    .intersect(&Interval::bounded(0, x - 1));
                let conjunction = NNFFormula::and(
                    lhs_simp
                        .get_intervals_in(&globally_interval)
                        .into_iter()
                        .map(|interval| {
                            NNFFormula::globally(
                                interval - Interval::singleton(t),
                                lhs_simp.at(*interval.lb().unwrap()).clone(),
                            )
                        })
                        .chain(std::iter::once(until)),
                );
                disjunction = NNFFormula::or([disjunction, conjunction]);
            }
            if t >= last_change {
                let rest = Interval::unbounded(t).intersect(unknown_interval);
                simp_signal.set(&rest, disjunction);
                break;
            } else {
                simp_signal.set(&Interval::singleton(t), disjunction);
            }
        }
        simp_signal
    }
}

fn interval_iter(&interval: &Interval<u32>) -> Box<dyn Iterator<Item = u32>> {
    match interval {
        Interval::Empty => Box::new(std::iter::empty()),
        Interval::Bounded { lb, ub } => Box::new(lb..=ub),
        Interval::Unbounded { lb } => Box::new(lb..),
    }
}

fn default_simp_mapping<T>(trace: &Trace<T, Kleene>) -> HashMap<NNFFormula<T>, FormulaSignal<T>>
where
    T: Integer + Unsigned + Copy + SaturatingSub + Hash,
{
    let mut mapping: HashMap<_, _> = trace
        .get_signals()
        .iter()
        .flat_map(|(name, signal)| {
            let positive = NNFFormula::AP(AtomicProposition {
                name: name.clone(),
                negated: false,
            });
            let pos_simp = signal.map(|v| match v {
                Kleene::True => NNFFormula::True,
                Kleene::False => NNFFormula::False,
                Kleene::Unknown => positive.clone(),
            });

            let negative = NNFFormula::AP(AtomicProposition {
                name: name.clone(),
                negated: true,
            });
            let neg_simp = signal.map(|v| match v {
                Kleene::True => NNFFormula::False,
                Kleene::False => NNFFormula::True,
                Kleene::Unknown => negative.clone(),
            });

            [(positive, pos_simp), (negative, neg_simp)]
        })
        .collect();
    mapping.insert(NNFFormula::True, Signal::uniform(NNFFormula::True));
    mapping.insert(NNFFormula::False, Signal::uniform(NNFFormula::False));
    mapping
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;

    #[test]
    fn test_until() {
        let a = AtomicProposition {
            name: Rc::from("a"),
            negated: false,
        };
        let b = AtomicProposition {
            name: Rc::from("b"),
            negated: false,
        };
        let c = AtomicProposition {
            name: Rc::from("c"),
            negated: false,
        };
        let d = AtomicProposition {
            name: Rc::from("d"),
            negated: false,
        };

        let unknown_interval = Interval::bounded(0, 1);

        let mut lhs_simp = Signal::indicator(
            &Interval::bounded(0, 2),
            NNFFormula::AP(a.clone()),
            NNFFormula::False,
        );
        lhs_simp.set(&Interval::bounded(3, 5), NNFFormula::AP(b.clone()));
        lhs_simp.set(&Interval::bounded(6, 10), NNFFormula::AP(c.clone()));

        let mut rhs_simp = Signal::indicator(
            &Interval::bounded(4, 7),
            NNFFormula::AP(d.clone()),
            NNFFormula::False,
        );
        rhs_simp.set(&Interval::bounded(9, 12), NNFFormula::AP(d.clone()));

        let until_interval = Interval::bounded(0, 5);

        let simp = Simplifier::<u32>::get_until_simplification(
            &unknown_interval,
            &lhs_simp,
            &until_interval,
            &rhs_simp,
        );
        println!("{}", simp.at(0));
        println!("{}", simp.at(1));
    }
}
