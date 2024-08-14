use std::{collections::HashMap, hash::Hash};

use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::NNFFormula,
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
            NNFFormula::Until(lhs, int, rhs) | NNFFormula::Release(lhs, int, rhs) => {
                let simp_sub_interval = *interval + *int;

                self.simplify_rec(lhs, &simp_sub_interval);
                self.simplify_rec(rhs, &simp_sub_interval);
                let lhs_simp = self.simplification_signals.get(lhs.as_ref()).unwrap();
                let rhs_simp = self.simplification_signals.get(rhs.as_ref()).unwrap();

                let mut simplification_signal = self.simp_sig_from_sat_sig(formula);
                Self::refine_unknowns_binary(
                    &mut simplification_signal,
                    interval,
                    lhs_simp,
                    int,
                    rhs_simp,
                    if matches!(formula, NNFFormula::Until(..)) {
                        Self::get_until_simplification
                    } else {
                        Self::get_release_simplification
                    },
                );
                simplification_signal
            }
        };
        self.simplification_signals
            .insert(formula, simplification_signal);
    }

    fn refine_unknowns_binary<F>(
        simplification_signal: &mut FormulaSignal<T>,
        relevant_interval: &Interval<T>,
        lhs_simp: &FormulaSignal<T>,
        formula_interval: &Interval<T>,
        rhs_simp: &FormulaSignal<T>,
        simplify_interval: F,
    ) where
        F: Fn(
            &Interval<T>,
            &FormulaSignal<T>,
            &Interval<T>,
            &FormulaSignal<T>,
        ) -> Signal<T, Option<NNFFormula<T>>>,
    {
        let unknown_intervals = simplification_signal
            .intervals_where(|f| !matches!(f, NNFFormula::True | NNFFormula::False))
            .into_iter()
            .map(|i| i.intersect(relevant_interval))
            .filter(|i| !i.is_empty());

        unknown_intervals
            .map(|unknown_interval| {
                simplify_interval(&unknown_interval, lhs_simp, formula_interval, rhs_simp)
            })
            .for_each(|simp| {
                simp.into_intervals_where(|opt| opt.is_some())
                    .into_iter()
                    .for_each(|(i, f)| {
                        simplification_signal.set(&i, f.unwrap());
                    })
            });
    }

    fn simp_sig_from_sat_sig(&self, formula: &NNFFormula<T>) -> FormulaSignal<T> {
        let satisfaction_signal = self
            .knowledge
            .satisfaction_signals()
            .get(formula)
            .expect("knowledge should contain all subformulas");
        satisfaction_signal.map(|kleene_value| match kleene_value {
            Kleene::True => NNFFormula::True,
            Kleene::False => NNFFormula::False,
            Kleene::Unknown => formula.clone(),
        })
    }

    fn get_globally_simplification(
        time: T,
        globally_interval: &Interval<T>,
        sub_simp: &FormulaSignal<T>,
    ) -> NNFFormula<T> {
        NNFFormula::and(
            sub_simp
                .get_intervals_in(globally_interval)
                .into_iter()
                .map(|interval| {
                    NNFFormula::globally(
                        interval - Interval::singleton(time),
                        sub_simp.at(*interval.lb().unwrap()).clone(),
                    )
                }),
        )
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
                let conjunction = NNFFormula::and([
                    Self::get_globally_simplification(t, &globally_interval, lhs_simp),
                    until,
                ]);
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

    fn get_release_simplification(
        unknown_interval: &Interval<T>,
        lhs_simp: &FormulaSignal<T>,
        release_interval: &Interval<T>,
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
            let omega = *release_interval + Interval::singleton(t);
            let splits = lhs_simp.get_refined_intervals_in(rhs_simp, &omega);
            let mut disjunction = Self::get_globally_simplification(
                t,
                &release_interval.minkowski_sum(Interval::singleton(t)),
                rhs_simp,
            );
            for split in splits {
                let x = *split.lb().expect("split should not be empty");
                let until = NNFFormula::until(
                    rhs_simp.at(x).clone(),
                    split - Interval::singleton(t),
                    NNFFormula::and([lhs_simp.at(x).clone(), rhs_simp.at(x).clone()]),
                );
                if matches!(until, NNFFormula::False) {
                    continue;
                }
                if x < T::one() {
                    disjunction = NNFFormula::or([disjunction, until]);
                    continue;
                }
                // [t + a, x - 1]
                let globally_interval = release_interval
                    .minkowski_sum(Interval::singleton(t))
                    .intersect(&Interval::bounded(T::zero(), x.saturating_sub(&T::one())));
                let conjunction = NNFFormula::and([
                    Self::get_globally_simplification(t, &globally_interval, rhs_simp),
                    until,
                ]);
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
    use std::{fs, rc::Rc};

    use rstest::*;

    use crate::{formula::AtomicProposition, parser::mltl_parser, trace_parser::trace_parser};

    use super::*;

    #[fixture]
    fn aps<T>() -> [NNFFormula<T>; 4] {
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

    #[rstest]
    fn test_until(aps: [NNFFormula<u32>; 4]) {
        let [a, b, c, d] = aps;

        let unknown_interval = Interval::bounded(0, 1);

        let mut lhs_simp =
            Signal::indicator(&Interval::bounded(0, 2), a.clone(), NNFFormula::False);
        lhs_simp.set(&Interval::bounded(3, 5), b.clone());
        lhs_simp.set(&Interval::bounded(6, 10), c.clone());

        let mut rhs_simp =
            Signal::indicator(&Interval::bounded(4, 7), d.clone(), NNFFormula::False);
        rhs_simp.set(&Interval::bounded(9, 12), d.clone());

        let until_interval = Interval::bounded(0, 5);

        let simp = Simplifier::<u32>::get_until_simplification(
            &unknown_interval,
            &lhs_simp,
            &until_interval,
            &rhs_simp,
        );
        assert_eq!(
            simp.at(0).as_ref().unwrap(),
            &mltl_parser::formula("(b U[4, 5] d) & (G[0, 2] a) & (X[3] b)")
                .unwrap()
                .into()
        );
        assert_eq!(
            simp.at(1).as_ref().unwrap(),
            &mltl_parser::formula(
                "((b U[3, 4] d) & (G[0, 1] a) & (X[2] b)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] d))"
            )
            .unwrap()
            .into()
        );
    }

    #[rstest]
    fn test_release(aps: [NNFFormula<u32>; 4]) {
        let [a, b, c, d] = aps;

        let unknown_interval = Interval::bounded(0, 1);

        let mut rhs_simp = Signal::indicator(&Interval::bounded(0, 2), a.clone(), NNFFormula::True);
        rhs_simp.set(&Interval::bounded(3, 5), b.clone());
        rhs_simp.set(&Interval::bounded(6, 10), c.clone());

        let mut lhs_simp =
            Signal::indicator(&Interval::bounded(4, 7), d.clone(), NNFFormula::False);
        lhs_simp.set(&Interval::bounded(9, 12), d.clone());

        let release_interval = Interval::bounded(0, 5);

        let simp = Simplifier::<u32>::get_release_simplification(
            &unknown_interval,
            &lhs_simp,
            &release_interval,
            &rhs_simp,
        );
        assert_eq!(
            simp.at(0).as_ref().unwrap(),
            &mltl_parser::formula(
                "((b U[4, 5] b & d) & (G[0, 2] a) & (X[3] b)) | ((G[0, 2] a) & (G[3, 5] b))"
            )
            .unwrap()
            .into()
        );
        assert_eq!(
            simp.at(1).as_ref().unwrap(),
            &mltl_parser::formula(
                "((b U[3, 4] b & d) & (G[0, 1] a) & (X[2] b)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] c)) | ((G[0, 1] a) & (G[2, 4] b) & (X[5] c & d))"
            )
            .unwrap()
            .into()
        );
    }

    #[rstest]
    fn test_example() {
        let phi = mltl_parser::formula("G (omc_e & front & oar & (F omc_o) -> !(!rl & (F rl)))")
            .expect("Syntax is correct")
            .into();
        let trace =
            trace_parser::trace(include_str!("../example_trace.txt")).expect("Syntax is correct");
        let mut simplifier = Simplifier::new(&phi, &trace);
        simplifier.simplify();
        let simplified = simplifier.simplification_signals.get(&phi).unwrap().at(0);
        println!("{}", simplified);
    }

    #[rstest]
    #[case("ri5")]
    #[case("rg1")]
    fn test_presimplified(#[case] rule: &str) {
        let presimplified_rule: NNFFormula<_> = mltl_parser::formula(
            fs::read_to_string(format!("{}.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct")
        .into();
        let naive_rule: NNFFormula<_> = mltl_parser::formula(
            fs::read_to_string(format!("{}_naive.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct")
        .into();
        let trace = trace_parser::trace(
            fs::read_to_string(format!("trace_{}.txt", rule).as_str())
                .expect("File exists")
                .as_str(),
        )
        .expect("Syntax is correct");
        let now = std::time::Instant::now();
        let mut simplifier = Simplifier::new(&naive_rule, &trace);
        simplifier.simplify();
        let simplified = simplifier
            .simplification_signals
            .get(&naive_rule)
            .unwrap()
            .at(0);
        println!("{:.2?}", now.elapsed());
        assert_eq!(&presimplified_rule, simplified);
    }
}
