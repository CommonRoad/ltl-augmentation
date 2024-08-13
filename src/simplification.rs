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
        &self,
        unknown_interval: &Interval<T>,
        lhs_simp: &FormulaSignal<T>,
        until_interval: &Interval<T>,
        rhs_simp: &FormulaSignal<T>,
    ) -> FormulaSignal<T> {
        let refined_intervals = lhs_simp
            .get_refined_intervals(rhs_simp)
            .into_iter()
            .map(|i| i.intersect(unknown_interval))
            .filter(|i| !i.is_empty())
            .collect_vec();
        for i in &refined_intervals {
            let lb = match i {
                Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => lb,
                Interval::Empty => {
                    unreachable!("all empty intervals should have been filtered out")
                }
            };
            let until_formula = |t| {
                let int = *i - Interval::singleton(t);
                NNFFormula::until(lhs_simp.at(*lb).clone(), int, rhs_simp.at(*lb).clone())
            };
            let affected = i.back_shift(*until_interval).intersect(unknown_interval);
        }
        let with_values = refined_intervals
            .into_iter()
            .map(|i| match i {
                Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => {
                    (i, lhs_simp.at(lb), rhs_simp.at(lb))
                }
                Interval::Empty => {
                    unreachable!("all empty intervals should have been filtered out")
                }
            })
            .collect_vec();
        // until_interval = [a, b]
        // Let t be a symbolic parameter for the time at which we evaluate the formula
        // Map lhs_simp by creating globally formula
        // G[lb - t, ub - t] lhs_simp
        // Combine lhs_simp and rhs_simp by creating until formula
        // lhs_simp U[lb - t, ub - t] rhs_simp
        // Take each of the until formulas and back shift by [a, b] to obtain the affected interval
        // Collect all globally formulas between lb of affected interval + a and ub of until formula interval
        todo!()
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
