use std::collections::{BTreeSet, HashMap};

use crate::clean::{
    formula::NNFFormula,
    monitoring::{kleene::KleeneMonitorSequence, monitor::Monitor},
    trace::Trace,
    truth_values::Kleene,
};

use super::{
    sequence::{knowledge::KnowledgeSequence, NormalizedSequence, Sequence, Time},
    sets::{interval::Interval, interval_set::IntervalSet},
};

type FormulaSequence = NormalizedSequence<Option<NNFFormula>>;

pub struct Augmenter<'a> {
    root: &'a NNFFormula,
    knowledge: KnowledgeSequence,
    monitor: Monitor<'a, Kleene>,
    augmentation_sequences: HashMap<&'a NNFFormula, FormulaSequence>,
}

impl<'a> Augmenter<'a> {
    pub fn new(formula: &'a NNFFormula, knowledge: KnowledgeSequence) -> Self {
        // Compute condensed and completed knowledge sequence
        let knowledge = knowledge.into_map(|kg| {
            let mut condensed = kg.condense_graph();
            condensed.complete_graph();
            condensed
        });

        // Precompute all monitoring results
        let aps = formula
            .collect_aps()
            .into_iter()
            .map(|ap| ap.name)
            .collect();
        let monitor = Monitor::new::<KleeneMonitorSequence>(formula, &knowledge.kleene_trace(&aps));

        Augmenter {
            root: formula,
            knowledge,
            monitor,
            augmentation_sequences: HashMap::new(),
        }
    }

    pub fn augment(&mut self) {
        self.augment_rec(self.root, &Interval::singleton(0).into())
    }

    fn augment_rec(&mut self, formula: &'a NNFFormula, relevant_steps: &IntervalSet) {
        let aug_seq = self
            .augmentation_sequences
            .entry(formula)
            .or_insert(FormulaSequence::uniform(None));

        if relevant_steps.is_empty() {
            return;
        }

        // Check the monitor result
        let verdicts = self
            .monitor
            .satisfaction_signals()
            .get(formula)
            .expect("Monitor should contain all subformulas");
        verdicts
            .intervals_where_eq(&Kleene::True)
            .iter()
            .for_each(|true_interval| aug_seq.set(true_interval, Some(NNFFormula::True)));
        verdicts
            .intervals_where_eq(&Kleene::False)
            .iter()
            .for_each(|false_interval| aug_seq.set(false_interval, Some(NNFFormula::False)));

        // Update the relevant steps: where the monitor did not return unknown, we no longer need a value
        let relevant_steps = relevant_steps.intersect(&IntervalSet::from_iter(
            verdicts.intervals_where_eq(&Kleene::Unknown),
        ));

        // Augment all subformulas
        let relevant_steps_subformulas = relevant_steps.minkowski_sum(&formula.get_interval());
        formula
            .iter_subformulas()
            .for_each(|sub| self.augment_rec(sub, &relevant_steps_subformulas));

        // Compute the augmentation of this formula for all remaining relevant steps
        match formula {
            NNFFormula::True | NNFFormula::False => self.augment_literal_trivial(formula),
            NNFFormula::AP(..) => self.augment_literal(formula, &relevant_steps),
            _ => self.augment_compound(formula, &relevant_steps),
        }
    }

    fn augment_literal_trivial(&mut self, literal: &NNFFormula) {
        let aug_seq = self.get_subformula_augmentation_mut(literal);
        aug_seq.set(&Interval::unbounded(0), Some(literal.clone()));
    }

    fn augment_literal(&mut self, literal: &NNFFormula, relevant_steps: &IntervalSet) {
        let aug_seq = self.get_subformula_augmentation_mut(literal);
        relevant_steps
            .get_intervals()
            .iter()
            .for_each(|interval| aug_seq.set(interval, Some(literal.clone())))
    }

    fn augment_compound(&mut self, formula: &NNFFormula, relevant_steps: &IntervalSet) {
        let last_change_subformulas = self
            .get_last_change_of_subformulas(formula, relevant_steps)
            .expect("Compound formula should have at least one subformula");

        for step in relevant_steps
            .get_intervals()
            .into_iter()
            .flat_map(|interval| interval.into_iter())
        {
            let augmentation = match formula {
                NNFFormula::And(subs) => self.augment_conjunction(subs, step),
                NNFFormula::Or(subs) => self.augment_disjunction(subs, step),
                NNFFormula::Until(lhs, interval, rhs) => {
                    self.augment_until(lhs, interval, rhs, step)
                }
                NNFFormula::Release(lhs, interval, rhs) => {
                    self.augment_release(lhs, interval, rhs, step)
                }
                _ => unreachable!("This function is only called for compound formulas"),
            };
            let aug_seq = self.get_subformula_augmentation_mut(formula);
            if step >= last_change_subformulas {
                relevant_steps
                    .intersect(&Interval::unbounded(0).into())
                    .get_intervals()
                    .iter()
                    .for_each(|interval| aug_seq.set(interval, Some(augmentation.clone())));
                return;
            } else {
                aug_seq.set(&Interval::singleton(step), Some(augmentation));
            }
        }
    }

    fn augment_conjunction(&self, subs: &BTreeSet<NNFFormula>, step: Time) -> NNFFormula {
        NNFFormula::and(subs.iter().map(|sub| {
            self.get_subformula_augmentation(sub)
                .at(step)
                .clone()
                .expect("Augmentation should have been computed")
        }))
    }

    fn augment_disjunction(&self, subs: &BTreeSet<NNFFormula>, step: Time) -> NNFFormula {
        NNFFormula::or(subs.iter().map(|sub| {
            self.get_subformula_augmentation(sub)
                .at(step)
                .clone()
                .expect("Augmentation should have been computed")
        }))
    }

    fn augment_globally<'b>(
        &'b self,
        sub: &NNFFormula,
        globally_interval: &Interval,
        step: Time,
    ) -> impl Iterator<Item = NNFFormula> + 'b {
        let step_interval = Interval::singleton(step);
        let sub_augmentation = self.get_subformula_augmentation(sub);
        sub_augmentation
            .interval_covering(&globally_interval.minkowski_sum(step_interval))
            .into_iter()
            .map(move |interval| {
                NNFFormula::globally(
                    interval - step_interval,
                    sub_augmentation
                        .at(*interval.lb().unwrap())
                        .clone()
                        .expect("Augmentation should have been computed"),
                )
            })
    }

    fn augment_until(
        &self,
        lhs: &NNFFormula,
        until_interval: &Interval,
        rhs: &NNFFormula,
        step: Time,
    ) -> NNFFormula {
        todo!()
    }

    fn augment_release(
        &self,
        lhs: &NNFFormula,
        release_interval: &Interval,
        rhs: &NNFFormula,
        step: Time,
    ) -> NNFFormula {
        let globally = NNFFormula::and(self.augment_globally(rhs, release_interval, step));
        let until = todo!();
    }

    fn get_last_change_of_subformulas(
        &mut self,
        formula: &NNFFormula,
        relevant_steps: &IntervalSet,
    ) -> Option<Time> {
        formula
            .iter_subformulas()
            .map(|sub| {
                let aug_seq = self.get_subformula_augmentation_mut(sub);
                aug_seq
                    .last_change_in(relevant_steps)
                    .expect("Relevant steps should not be empty")
            })
            .max()
    }

    fn get_subformula_augmentation(&self, subformula: &NNFFormula) -> &FormulaSequence {
        self.augmentation_sequences
            .get(subformula)
            .expect("Formula should have been inserted before")
    }

    fn get_subformula_augmentation_mut(&mut self, subformula: &NNFFormula) -> &mut FormulaSequence {
        self.augmentation_sequences
            .get_mut(subformula)
            .expect("Formula should have been inserted before")
    }

    // fn simplify_rec(&mut self, formula: &'a NNFFormula<Time>, interval: &Interval<Time>) {
    //     let simplification_signal = match formula {
    //         NNFFormula::True | NNFFormula::False | NNFFormula::AP(_) => {
    //             self.simp_sig_from_sat_sig(formula)
    //         }
    //         NNFFormula::And(subs) | NNFFormula::Or(subs) => {
    //             subs.iter().for_each(|sub| self.simplify_rec(sub, interval));
    //             let it = subs
    //                 .iter()
    //                 .map(|sub| self.simplification_signals.get(sub).unwrap());
    //             if matches!(formula, NNFFormula::And(..)) {
    //                 it.fold(Signal::uniform(NNFFormula::True), |acc, sig| {
    //                     acc.combine(sig, |f1, f2| NNFFormula::and([f1.clone(), f2.clone()]))
    //                 })
    //             } else {
    //                 it.fold(Signal::uniform(NNFFormula::False), |acc, sig| {
    //                     acc.combine(sig, |f1, f2| NNFFormula::or([f1.clone(), f2.clone()]))
    //                 })
    //             }
    //         }
    //         NNFFormula::Until(lhs, int, rhs) | NNFFormula::Release(lhs, int, rhs) => {
    //             let simp_sub_interval = *interval + *int;

    //             self.simplify_rec(lhs, &simp_sub_interval);
    //             self.simplify_rec(rhs, &simp_sub_interval);
    //             let lhs_simp = self.simplification_signals.get(lhs.as_ref()).unwrap();
    //             let rhs_simp = self.simplification_signals.get(rhs.as_ref()).unwrap();

    //             let mut simplification_signal = self.simp_sig_from_sat_sig(formula);
    //             Self::refine_unknowns_binary(
    //                 &mut simplification_signal,
    //                 interval,
    //                 lhs_simp,
    //                 int,
    //                 rhs_simp,
    //                 if matches!(formula, NNFFormula::Until(..)) {
    //                     Self::get_until_simplification
    //                 } else {
    //                     Self::get_release_simplification
    //                 },
    //             );
    //             simplification_signal
    //         }
    //     };
    //     self.simplification_signals
    //         .insert(formula, simplification_signal);
    // }

    // fn refine_unknowns_binary<F>(
    //     simplification_signal: &mut FormulaSignal,
    //     relevant_interval: &Interval<Time>,
    //     lhs_simp: &FormulaSignal,
    //     formula_interval: &Interval<Time>,
    //     rhs_simp: &FormulaSignal,
    //     simplify_interval: F,
    // ) where
    //     F: Fn(
    //         &Interval<Time>,
    //         &FormulaSignal,
    //         &Interval<Time>,
    //         &FormulaSignal,
    //     ) -> Signal<Time, Option<NNFFormula<Time>>>,
    // {
    //     let unknown_intervals = simplification_signal
    //         .intervals_where(|f| !matches!(f, NNFFormula::True | NNFFormula::False))
    //         .into_iter()
    //         .map(|i| i.intersect(relevant_interval))
    //         .filter(|i| !i.is_empty());

    //     unknown_intervals
    //         .map(|unknown_interval| {
    //             simplify_interval(&unknown_interval, lhs_simp, formula_interval, rhs_simp)
    //         })
    //         .for_each(|simp| {
    //             simp.into_intervals_where(|opt| opt.is_some())
    //                 .into_iter()
    //                 .for_each(|(i, f)| {
    //                     simplification_signal.set(&i, f.unwrap());
    //                 })
    //         });
    // }

    // fn simp_sig_from_sat_sig(&self, formula: &NNFFormula<Time>) -> FormulaSignal {
    //     let satisfaction_signal = self
    //         .monitor
    //         .satisfaction_signals()
    //         .get(formula)
    //         .expect("knowledge should contain all subformulas");
    //     satisfaction_signal.map(|kleene_value| match kleene_value {
    //         Kleene::True => NNFFormula::True,
    //         Kleene::False => NNFFormula::False,
    //         Kleene::Unknown => formula.clone(),
    //     })
    // }

    // fn get_until_simplification(
    //     unknown_interval: &Interval<Time>,
    //     lhs_simp: &FormulaSignal,
    //     until_interval: &Interval<Time>,
    //     rhs_simp: &FormulaSignal,
    // ) -> Signal<Time, Option<NNFFormula<Time>>> {
    //     Self::get_binary_simplification(
    //         unknown_interval,
    //         lhs_simp,
    //         until_interval,
    //         rhs_simp,
    //         |_| NNFFormula::False,
    //         |_, rhs| rhs.clone(),
    //         lhs_simp,
    //     )
    // }

    // fn get_release_simplification(
    //     unknown_interval: &Interval<Time>,
    //     lhs_simp: &FormulaSignal,
    //     release_interval: &Interval<Time>,
    //     rhs_simp: &FormulaSignal,
    // ) -> Signal<Time, Option<NNFFormula<Time>>> {
    //     Self::get_binary_simplification(
    //         unknown_interval,
    //         lhs_simp,
    //         release_interval,
    //         rhs_simp,
    //         |t| {
    //             NNFFormula::and(Self::get_globally_simplification(
    //                 t,
    //                 &release_interval.minkowski_sum(Interval::singleton(t)),
    //                 rhs_simp,
    //             ))
    //         },
    //         |lhs, rhs| NNFFormula::and([lhs.clone(), rhs.clone()]),
    //         rhs_simp,
    //     )
    // }

    // fn get_binary_simplification<F, G>(
    //     unknown_interval: &Interval<Time>,
    //     lhs_simp: &FormulaSignal,
    //     binary_interval: &Interval<Time>,
    //     rhs_simp: &FormulaSignal,
    //     get_initial_disjunction: F,
    //     get_eventuality: G,
    //     universality: &FormulaSignal,
    // ) -> Signal<Time, Option<NNFFormula<Time>>>
    // where
    //     F: Fn(Time) -> NNFFormula<Time>,
    //     G: Fn(&NNFFormula<Time>, &NNFFormula<Time>) -> NNFFormula<Time>,
    // {
    //     let mut simp_signal = Signal::uniform(None);

    //     let last_change = lhs_simp.last_change().max(rhs_simp.last_change());
    //     let mut it = unknown_interval
    //         .intersect(&Interval::bounded(0, last_change))
    //         .into_iter()
    //         .peekable();
    //     while let Some(t) = it.next() {
    //         let relevant_interval = *binary_interval + Interval::singleton(t);

    //         let constant_intervals =
    //             lhs_simp.get_refined_intervals_in(rhs_simp, &relevant_interval);
    //         let disjunction = constant_intervals.into_iter().filter_map(|c_int| {
    //             let c_int_lb = *c_int.lb().expect("constant interval should not be empty");

    //             // eventuality has to hold somewhere c_int - [t, t], and the universality until then
    //             let eventuality = get_eventuality(lhs_simp.at(c_int_lb), rhs_simp.at(c_int_lb));
    //             let until = NNFFormula::until(
    //                 universality.at(c_int_lb).clone(),
    //                 c_int - Interval::singleton(t),
    //                 eventuality,
    //             );
    //             if matches!(until, NNFFormula::False) {
    //                 return None;
    //             }

    //             // universality needs to hold in [t + a, x - 1], where a is the lower bound of binary_interval
    //             let globally_interval =
    //                 relevant_interval.intersect(&Interval::bounded_ub_excl(0, c_int_lb));
    //             Some(NNFFormula::and(
    //                 Self::get_globally_simplification(t, &globally_interval, universality)
    //                     .into_iter()
    //                     .chain(std::iter::once(until)),
    //             ))
    //         });
    //         let disjunction =
    //             NNFFormula::or(disjunction.chain(std::iter::once(get_initial_disjunction(t))));

    //         if it.peek().is_none() {
    //             // Last iteration
    //             let rest = Interval::unbounded(t).intersect(unknown_interval);
    //             simp_signal.set(&rest, Some(disjunction));
    //         } else {
    //             simp_signal.set(&Interval::singleton(t), Some(disjunction));
    //         }
    //     }
    //     simp_signal
    // }

    // fn get_globally_simplification(
    //     time: Time,
    //     globally_interval: &Interval<Time>,
    //     sub_simp: &FormulaSignal,
    // ) -> Vec<NNFFormula<Time>> {
    //     sub_simp
    //         .get_intervals_in(globally_interval)
    //         .into_iter()
    //         .map(|interval| {
    //             NNFFormula::globally(
    //                 interval - Interval::singleton(time),
    //                 sub_simp.at(*interval.lb().unwrap()).clone(),
    //             )
    //         })
    //         .collect()
    // }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use rstest::*;

    use crate::clean::formula::AtomicProposition;

    use super::*;

    #[fixture]
    fn aps() -> [NNFFormula; 4] {
        let a = NNFFormula::AP(AtomicProposition {
            name: Rc::from("a"),
            negated: false,
        });
        let b = NNFFormula::AP(AtomicProposition {
            name: Rc::from("b"),
            negated: false,
        });
        let c = NNFFormula::AP(AtomicProposition {
            name: Rc::from("c"),
            negated: false,
        });
        let d = NNFFormula::AP(AtomicProposition {
            name: Rc::from("d"),
            negated: false,
        });
        [a, b, c, d]
    }

    // #[rstest]
    // fn test_until(aps: [NNFFormula<u32>; 4]) {
    //     let [a, b, c, d] = aps;

    //     let unknown_interval = Interval::bounded(0, 1);

    //     let mut lhs_simp =
    //         Signal::indicator(&Interval::bounded(0, 2), a.clone(), NNFFormula::False);
    //     lhs_simp.set(&Interval::bounded(3, 5), b.clone());
    //     lhs_simp.set(&Interval::bounded(6, 10), c.clone());

    //     let mut rhs_simp =
    //         Signal::indicator(&Interval::bounded(4, 7), d.clone(), NNFFormula::False);
    //     rhs_simp.set(&Interval::bounded(9, 12), d.clone());

    //     let until_interval = Interval::bounded(0, 5);

    //     let simp = Simplifier::get_until_simplification(
    //         &unknown_interval,
    //         &lhs_simp,
    //         &until_interval,
    //         &rhs_simp,
    //     );
    //     assert_eq!(
    //         simp.at(0).as_ref().unwrap(),
    //         &mltl_parser::formula("(b U[4, 5] d) & (G[0, 2] a) & (X[3] b)")
    //             .unwrap()
    //             .into()
    //     );
    //     assert_eq!(
    //         simp.at(1).as_ref().unwrap(),
    //         &mltl_parser::formula(
    //             "((b U[3, 4] d) & (G[0, 1] a) & (X[2] b)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] d))"
    //         )
    //         .unwrap()
    //         .into()
    //     );
    // }

    // #[rstest]
    // fn test_release(aps: [NNFFormula<u32>; 4]) {
    //     let [a, b, c, d] = aps;

    //     let unknown_interval = Interval::bounded(0, 1);

    //     let mut rhs_simp = Signal::indicator(&Interval::bounded(0, 2), a.clone(), NNFFormula::True);
    //     rhs_simp.set(&Interval::bounded(3, 5), b.clone());
    //     rhs_simp.set(&Interval::bounded(6, 10), c.clone());

    //     let mut lhs_simp =
    //         Signal::indicator(&Interval::bounded(4, 7), d.clone(), NNFFormula::False);
    //     lhs_simp.set(&Interval::bounded(9, 12), d.clone());

    //     let release_interval = Interval::bounded(0, 5);

    //     let simp = Simplifier::get_release_simplification(
    //         &unknown_interval,
    //         &lhs_simp,
    //         &release_interval,
    //         &rhs_simp,
    //     );
    //     assert_eq!(
    //         simp.at(0).as_ref().unwrap(),
    //         &mltl_parser::formula(
    //             "((b U[4, 5] b & d) & (G[0, 2] a) & (X[3] b)) | ((G[0, 2] a) & (G[3, 5] b))"
    //         )
    //         .unwrap()
    //         .into()
    //     );
    //     assert_eq!(
    //         simp.at(1).as_ref().unwrap(),
    //         &mltl_parser::formula(
    //             "((b U[3, 4] b & d) & (G[0, 1] a) & (X[2] b)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] c)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] c & d))"
    //         )
    //         .unwrap()
    //         .into()
    //     );
    // }

    // #[rstest]
    // fn test_example() {
    //     let phi = mltl_parser::formula("G (omc_e & front & oar & (F omc_o) -> !(!rl & (F rl)))")
    //         .expect("Syntax is correct")
    //         .into();
    //     let trace =
    //         trace_parser::trace(include_str!("../example_trace.txt")).expect("Syntax is correct");
    //     let mut simplifier = Simplifier::new(&phi, &trace);
    //     simplifier.simplify();
    //     let simplified = simplifier.simplification_signals.get(&phi).unwrap().at(0);
    //     println!("{}", simplified);
    //     println!("{:?}", simplified.collect_aps_with_time());
    // }

    // #[rstest]
    // #[case("ri5")]
    // #[case("rg1")]
    // fn test_presimplified(#[case] rule: &str) {
    //     let presimplified_rule: NNFFormula<_> = mltl_parser::formula(
    //         fs::read_to_string(format!("{}.txt", rule).as_str())
    //             .expect("File exists")
    //             .as_str(),
    //     )
    //     .expect("Syntax is correct")
    //     .into();
    //     let naive_rule: NNFFormula<_> = mltl_parser::formula(
    //         fs::read_to_string(format!("{}_naive.txt", rule).as_str())
    //             .expect("File exists")
    //             .as_str(),
    //     )
    //     .expect("Syntax is correct")
    //     .into();
    //     let trace = trace_parser::trace(
    //         fs::read_to_string(format!("trace_{}.txt", rule).as_str())
    //             .expect("File exists")
    //             .as_str(),
    //     )
    //     .expect("Syntax is correct");
    //     let now = std::time::Instant::now();
    //     let mut simplifier = Simplifier::new(&naive_rule, &trace);
    //     simplifier.simplify();
    //     let simplified = simplifier
    //         .simplification_signals
    //         .get(&naive_rule)
    //         .unwrap()
    //         .at(0);
    //     println!("{:.2?}", now.elapsed());
    //     // assert_eq!(&presimplified_rule, simplified);
    //     println!("{}", simplified.clone().move_next_inwards());
    // }
}
