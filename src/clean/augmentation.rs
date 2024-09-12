use std::collections::{BTreeSet, HashMap};

use super::{
    sequence::{knowledge::KnowledgeSequence, NormalizedSequence, Sequence, Time},
    sets::{interval::Interval, interval_set::IntervalSet},
};
use crate::clean::formula::literal::Literal;
use crate::clean::formula::nnf::NNFFormula;
use crate::clean::{
    monitoring::{kleene::KleeneMonitorSequence, monitor::Monitor},
    truth_values::Kleene,
};

type FormulaSequence = NormalizedSequence<Option<NNFFormula>>;

pub struct Augmenter {
    knowledge: KnowledgeSequence,
    monitor: Monitor<Kleene>,
}

impl Augmenter {
    pub fn new(knowledge: KnowledgeSequence) -> Self {
        // Compute condensed and completed knowledge sequence
        let knowledge = knowledge.into_map(|kg| {
            let mut condensed = kg.condense_graph();
            condensed.complete_graph();
            condensed
        });

        let trace = knowledge.kleene_trace();
        let monitor = Monitor::with_default(trace, Kleene::Unknown);

        Augmenter { knowledge, monitor }
    }

    pub fn augment(&self, formula: &NNFFormula) -> NNFFormula {
        self.augment_in(formula, &Interval::singleton(0).into())
            .remove(formula)
            .and_then(|seq| seq.at(0).as_ref().cloned())
            .expect("Augmentation at time 0 should have been computed")
    }

    pub fn augment_in<'a>(
        &self,
        formula: &'a NNFFormula,
        time_steps: &IntervalSet,
    ) -> HashMap<&'a NNFFormula, FormulaSequence> {
        // Precompute all monitoring results
        let satisfaction_sequences = self.monitor.evaluate::<KleeneMonitorSequence>(formula);

        let mut augmentation_sequences = HashMap::new();
        let mut context = AugmentationContext {
            root: formula,
            knowledge: &self.knowledge,
            satisfaction_sequencs: &satisfaction_sequences,
            augmentation_sequences: &mut augmentation_sequences,
        };

        context.augment_in(time_steps);

        augmentation_sequences
    }
}

struct AugmentationContext<'a, 'b> {
    root: &'a NNFFormula,
    knowledge: &'b KnowledgeSequence,
    satisfaction_sequencs: &'b HashMap<&'a NNFFormula, NormalizedSequence<Kleene>>,
    augmentation_sequences: &'b mut HashMap<&'a NNFFormula, FormulaSequence>,
}

impl<'a, 'b> AugmentationContext<'a, 'b> {
    pub fn augment_in(&mut self, time_steps: &IntervalSet) {
        self.augment_rec(self.root, time_steps)
    }

    fn augment_rec(&mut self, formula: &'a NNFFormula, relevant_steps: &IntervalSet) {
        if !self.augmentation_sequences.contains_key(formula) {
            self.augmentation_sequences
                .insert(formula, FormulaSequence::uniform(None));

            // Write the monitoring result to the augmentation sequence
            let aug_seq = self.augmentation_sequences.get_mut(formula).unwrap();
            let verdicts = self
                .satisfaction_sequencs
                .get(formula)
                .expect("Monitor should contain all subformulas");
            verdicts
                .intervals_where_eq(&Kleene::True)
                .iter()
                .for_each(|true_interval| {
                    aug_seq.set(true_interval, Some(NNFFormula::true_literal()))
                });
            verdicts
                .intervals_where_eq(&Kleene::False)
                .iter()
                .for_each(|false_interval| {
                    aug_seq.set(false_interval, Some(NNFFormula::false_literal()))
                });
        }

        // Update the relevant steps: we only need a value where we don't already have one
        let aug_seq = self.augmentation_sequences.get(&formula).unwrap();
        let relevant_steps = relevant_steps.intersect(&IntervalSet::from_iter(
            aug_seq.intervals_where(Option::is_none),
        ));
        if relevant_steps.is_empty() {
            return;
        }

        // Augment all subformulas
        let relevant_steps_subformulas = relevant_steps.minkowski_sum(&formula.get_interval());
        for subformula in formula.iter_subformulas() {
            self.augment_rec(subformula, &relevant_steps_subformulas)
        }

        // Compute the augmentation of this formula for all remaining relevant steps
        match formula {
            NNFFormula::Literal(..) => self.augment_literal(formula, &relevant_steps),
            _ => self.augment_compound(formula, &relevant_steps, &relevant_steps_subformulas),
        }
    }

    fn augment_literal(&mut self, formula: &NNFFormula, relevant_steps: &IntervalSet) {
        match formula {
            NNFFormula::Literal(Literal::True) | NNFFormula::Literal(Literal::False) => self
                .get_subformula_augmentation_mut(formula)
                .set(&Interval::unbounded(0), Some(formula.clone())),
            NNFFormula::Literal(literal @ Literal::Atom(..)) => {
                self.augment_atomic_proposition(formula, literal, relevant_steps)
            }
            _ => unreachable!("This function is only called for literals"),
        }
    }

    fn augment_atomic_proposition(
        &mut self,
        formula: &NNFFormula,
        literal: &Literal,
        relevant_steps: &IntervalSet,
    ) {
        // We cannot use get_subformula_augmentation_mut here, because this would borrow all of self as mutable
        let aug_seq = self
            .augmentation_sequences
            .get_mut(formula)
            .expect("Formula should have been inserted before");
        for interval in relevant_steps
            .get_intervals()
            .iter()
            .flat_map(|interval| self.knowledge.interval_covering(interval))
        {
            let kg = self.knowledge.at(*interval.lb().unwrap());
            let augmentation = NNFFormula::or(
                kg.implying_representatives(literal)
                    .into_iter()
                    .map(|l| NNFFormula::Literal(l.clone())),
            );
            aug_seq.set(&interval, Some(augmentation));
        }
    }

    fn augment_compound(
        &mut self,
        formula: &NNFFormula,
        relevant_steps: &IntervalSet,
        relevant_steps_subformulas: &IntervalSet,
    ) {
        let last_change_subformulas = self
            .get_last_change_of_subformulas(formula, relevant_steps_subformulas)
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
                NNFFormula::Globally(interval, sub) => self.augment_globally(sub, interval, step),
                _ => unreachable!("This function is only called for compound formulas"),
            };
            let aug_seq = self.get_subformula_augmentation_mut(formula);
            if step >= last_change_subformulas {
                relevant_steps
                    .intersect(&Interval::unbounded(step).into())
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

    fn augment_globally(
        &self,
        sub: &NNFFormula,
        globally_interval: &Interval,
        step: Time,
    ) -> NNFFormula {
        let sub_augmentation = self.get_subformula_augmentation(sub);
        NNFFormula::and(Self::augment_globally_seq(
            sub_augmentation,
            globally_interval,
            step,
        ))
    }

    fn augment_globally_seq<'z>(
        sub: &'z FormulaSequence,
        globally_interval: &Interval,
        step: Time,
    ) -> impl Iterator<Item = NNFFormula> + 'z {
        let step_interval = Interval::singleton(step);
        sub.interval_covering(&globally_interval.minkowski_sum(step_interval))
            .into_iter()
            .map(move |interval| {
                NNFFormula::globally(
                    interval - step_interval,
                    sub.at(*interval.lb().unwrap())
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
        let lhs_augmentation = self.get_subformula_augmentation(lhs);
        let rhs_augmentation = self.get_subformula_augmentation(rhs);
        Self::augment_until_seq(lhs_augmentation, until_interval, rhs_augmentation, step)
    }

    fn augment_until_seq(
        lhs: &FormulaSequence,
        until_interval: &Interval,
        rhs: &FormulaSequence,
        step: Time,
    ) -> NNFFormula {
        let step_interval = Interval::singleton(step);
        NNFFormula::or(
            lhs.refined_interval_covering(rhs, &until_interval.minkowski_sum(step_interval))
                .into_iter()
                .map(|interval| {
                    let interval_lb = *interval.lb().unwrap();
                    let until = NNFFormula::until(
                        lhs.at(interval_lb)
                            .clone()
                            .expect("Augmentation should have been computed"),
                        interval - step_interval,
                        rhs.at(interval_lb)
                            .clone()
                            .expect("Augmentation should have been computed"),
                    );
                    if interval_lb > step {
                        let globally = Self::augment_globally_seq(
                            lhs,
                            &Interval::bounded_ub_excl(
                                *until_interval.lb().unwrap(),
                                interval_lb - step,
                            ),
                            step,
                        );
                        NNFFormula::and(globally.chain(std::iter::once(until)))
                    } else {
                        until
                    }
                }),
        )
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
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use rstest::*;

    use super::*;
    use crate::clean::formula::atomic_proposition::AtomicProposition;
    use crate::clean::formula::parser::mltl_parser;
    use crate::clean::trace::parser::kleene_trace_parser;

    #[fixture]
    fn aps() -> [NNFFormula; 4] {
        let a = NNFFormula::Literal(Literal::Atom(AtomicProposition {
            name: Arc::from("a"),
            negated: false,
        }));
        let b = NNFFormula::Literal(Literal::Atom(AtomicProposition {
            name: Arc::from("b"),
            negated: false,
        }));
        let c = NNFFormula::Literal(Literal::Atom(AtomicProposition {
            name: Arc::from("c"),
            negated: false,
        }));
        let d = NNFFormula::Literal(Literal::Atom(AtomicProposition {
            name: Arc::from("d"),
            negated: false,
        }));
        [a, b, c, d]
    }

    #[rstest]
    fn test_until(aps: [NNFFormula; 4]) {
        let [a, b, c, d] = aps;

        let mut lhs_simp = FormulaSequence::indicator(
            &Interval::bounded(0, 2),
            Some(a.clone()),
            Some(NNFFormula::false_literal()),
        );
        lhs_simp.set(&Interval::bounded(3, 5), Some(b.clone()));
        lhs_simp.set(&Interval::bounded(6, 10), Some(c.clone()));

        let mut rhs_simp = FormulaSequence::indicator(
            &Interval::bounded(4, 7),
            Some(d.clone()),
            Some(NNFFormula::false_literal()),
        );
        rhs_simp.set(&Interval::bounded(9, 12), Some(d.clone()));

        let until_interval = Interval::bounded(0, 5);

        let augmented_0 =
            AugmentationContext::augment_until_seq(&lhs_simp, &until_interval, &rhs_simp, 0);
        assert_eq!(
            augmented_0,
            mltl_parser::formula("(b U[4, 5] d) & (G[0, 2] a) & (X[3] b)")
                .unwrap()
                .into()
        );
        let augmented_1 =
            AugmentationContext::augment_until_seq(&lhs_simp, &until_interval, &rhs_simp, 1);
        assert_eq!(
            augmented_1,
            mltl_parser::formula(
                "((b U[3, 4] d) & (G[0, 1] a) & (X[2] b)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] d))"
            )
            .unwrap()
            .into()
        );
    }

    #[rstest]
    fn test_globally(aps: [NNFFormula; 4]) {
        let [a, b, c, _] = aps;

        let mut sub_simp = FormulaSequence::indicator(
            &Interval::bounded(0, 1),
            Some(a.clone()),
            Some(NNFFormula::true_literal()),
        );
        sub_simp.set(&Interval::bounded(3, 5), Some(b.clone()));
        sub_simp.set(&Interval::bounded(6, 10), Some(c.clone()));

        let globally_interval = Interval::bounded(0, 5);

        let augmented_0 = NNFFormula::and(AugmentationContext::augment_globally_seq(
            &sub_simp,
            &globally_interval,
            0,
        ));
        assert_eq!(
            augmented_0,
            mltl_parser::formula("(G[0, 1] a) & (G[3, 5] b)")
                .unwrap()
                .into()
        );
        let augmented_1 = NNFFormula::and(AugmentationContext::augment_globally_seq(
            &sub_simp,
            &globally_interval,
            1,
        ));
        assert_eq!(
            augmented_1,
            mltl_parser::formula("a & (G[2, 4] b) & (X[5] c)")
                .unwrap()
                .into()
        );
    }

    #[rstest]
    fn test_example() {
        let phi = mltl_parser::formula("G (omc_e & front & oar & (F omc_o) -> !(!rl & (F rl)))")
            .expect("Syntax is correct")
            .into();

        let trace = kleene_trace_parser::trace(include_str!("../../example_trace.txt"))
            .expect("Syntax is correct");
        let knowledge = KnowledgeSequence::from(trace);
        let augmenter = Augmenter::new(knowledge);
        let augmented = augmenter.augment(&phi);
        let expected = mltl_parser::formula("(G[0, 4] (F rl) -> rl) & (G[5, 7] front -> !(!rl & (F rl))) & (G[8, 15] omc_e & front -> !(!rl & (F rl))) & (G[16,*] omc_e & front & oar & (F omc_o) -> !(!rl & (F rl)))")
            .expect("Syntax is correct")
            .into();
        println!("{}", augmented);
        assert_eq!(augmented, expected);
    }

    #[rstest]
    #[case("ri5")]
    #[case("rg1")]
    fn test_preaugmented(#[case] rule: &str) {
        use std::fs;

        let preaugmented_rule: NNFFormula = mltl_parser::formula(
            fs::read_to_string(format!("{}.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct")
        .into();
        let naive_rule: NNFFormula = mltl_parser::formula(
            fs::read_to_string(format!("{}_naive.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct")
        .into();
        let trace = kleene_trace_parser::trace(
            fs::read_to_string(format!("trace_{}.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct");
        let knowledge = KnowledgeSequence::from(trace);

        let now = std::time::Instant::now();
        let augmenter = Augmenter::new(knowledge);
        let augmented = augmenter.augment(&naive_rule);
        println!("{:.2?}", now.elapsed());

        // println!("{}", augmented);
        assert_eq!(preaugmented_rule, augmented);
    }
}
