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

                let satisfaction_signal = self
                    .knowledge
                    .satisfaction_signals()
                    .get(formula)
                    .expect("knowledge should contain all subformulas");
                let unknown_intervals = satisfaction_signal
                    .intervals_where_eq(&Kleene::Unknown)
                    .into_iter()
                    .map(|i| i.intersect(int))
                    .filter(|i| !i.is_empty());

                let mut simplification_signal =
                    satisfaction_signal.map(|kleene_value| match kleene_value {
                        Kleene::True => NNFFormula::True,
                        Kleene::False => NNFFormula::False,
                        Kleene::Unknown => formula.clone(),
                    });

                unknown_intervals
                    .map(|unknown_interval| {
                        Self::get_until_simplification(&unknown_interval, lhs_simp, int, rhs_simp)
                    })
                    .for_each(|simp| {
                        simp.into_intervals_where(|opt| opt.is_some())
                            .into_iter()
                            .for_each(|(i, f)| {
                                simplification_signal.set(&i, f.unwrap());
                            })
                    });
                todo!()
            }
            _ => todo!(),
        };
        self.simplification_signals
            .insert(formula, simplification_signal);
    }

    fn get_until_simplification(
        unknown_interval: &Interval<T>,
        lhs_simp: &FormulaSignal<T>,
        until_interval: &Interval<T>,
        rhs_simp: &FormulaSignal<T>,
    ) -> Signal<T, Option<NNFFormula<T>>> {
        let last_change = lhs_simp.last_change().max(rhs_simp.last_change());
        let mut simp_signal = Signal::uniform(None);
        if unknown_interval.is_empty() {
            return simp_signal;
        }
        let mut t = *unknown_interval.lb().unwrap();
        let ub = unknown_interval.ub();
        while ub.map(|&ub| t <= ub).unwrap_or(true) {
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
                if x < T::one() {
                    disjunction = NNFFormula::or([disjunction, until]);
                    continue;
                }
                // [t + a, x - 1]
                let globally_interval = until_interval
                    .minkowski_sum(Interval::singleton(t))
                    .intersect(&Interval::bounded(T::zero(), x.saturating_sub(&T::one())));
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
                simp_signal.set(&rest, Some(disjunction));
                break;
            } else {
                simp_signal.set(&Interval::singleton(t), Some(disjunction));
                t.inc();
            }
        }
        simp_signal
    }
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
        println!("{}", simp.at(0).as_ref().unwrap());
        println!("{}", simp.at(1).as_ref().unwrap());
    }
}
