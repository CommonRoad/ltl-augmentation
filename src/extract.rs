use std::{
    collections::{BTreeSet, HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    monitoring::{kleene::KleeneMonitorSignal, monitor::Monitor},
    sets::{interval::Interval, interval_set::IntervalSet},
    signals::truth_values::Kleene,
    trace::Trace,
};

#[derive(Debug, Clone)]
struct NecessaryIntervals<T>(HashMap<AtomicProposition, IntervalSet<T>>);

impl<T> Default for NecessaryIntervals<T> {
    fn default() -> Self {
        NecessaryIntervals(HashMap::new())
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> NecessaryIntervals<T> {
    fn merge(&mut self, other: Self, f: impl Fn(IntervalSet<T>, IntervalSet<T>) -> IntervalSet<T>) {
        self.0.merge(other.0, f);
    }

    fn union(mut self, other: Self) -> Self {
        self.merge(other, |i1, i2| i1.union(&i2));
        self
    }

    fn intersect(mut self, other: Self) -> Self {
        self.merge(other, |i1, i2| i1.intersect(&i2));
        self
    }

    fn minkowski_sum_intersection(self, interval: &Interval<T>) -> Self {
        NecessaryIntervals(
            self.0
                .into_iter()
                .map(|(ap, i)| (ap, i.minkowski_sum_intersection(interval)))
                .collect(),
        )
    }

    fn minkowski_sum(self, interval: &Interval<T>) -> Self {
        NecessaryIntervals(
            self.0
                .into_iter()
                .map(|(ap, i)| (ap, i.minkowski_sum(interval)))
                .collect(),
        )
    }
}

struct KnowledgeProvider<'a, T> {
    knowledge: Monitor<'a, T, Kleene>,
    contraction: Interval<T>,
}

impl<'a, T: Integer + Unsigned + Copy + SaturatingSub + Hash> KnowledgeProvider<'a, T> {
    fn new(formula: &'a NNFFormula<T>, trace: &Trace<T, Kleene>) -> Self {
        let knowledge = Monitor::new::<KleeneMonitorSignal<_>>(formula, trace);
        KnowledgeProvider {
            knowledge,
            contraction: Interval::singleton(T::zero()),
        }
    }

    fn contract(&mut self, interval: &Interval<T>) {
        self.contraction = self.contraction + *interval;
    }

    fn uncontract(&mut self, interval: &Interval<T>) {
        self.contraction = self.contraction.minkowski_difference(*interval);
    }

    fn get_cannot(&self, formula: &'a NNFFormula<T>) -> Option<IntervalSet<T>> {
        self.knowledge
            .satisfaction_signals()
            .get(formula)
            .map(|sig| {
                sig.intervals_where_eq(&Kleene::False)
                    .into_iter()
                    .map(|i| i.minkowski_difference(self.contraction))
                    .collect()
            })
    }
}

type ExtractionCache<'a, T> =
    HashMap<(&'a NNFFormula<T>, Rc<IntervalSet<T>>), NecessaryIntervals<T>>;
pub struct NecessaryIntervalExtractor<'a, T> {
    formula: &'a NNFFormula<T>,
    knowledge_provider: KnowledgeProvider<'a, T>,
    cache: ExtractionCache<'a, T>,
}

impl<'a, T: Integer + Unsigned + Copy + Hash + SaturatingSub + std::fmt::Debug>
    NecessaryIntervalExtractor<'a, T>
{
    pub fn new(formula: &'a NNFFormula<T>, trace: &Trace<T, Kleene>) -> Self {
        let knowledge_provider = KnowledgeProvider::new(formula, trace);
        NecessaryIntervalExtractor {
            formula,
            knowledge_provider,
            cache: HashMap::new(),
        }
    }

    pub fn extract(
        &mut self,
        holds_in: IntervalSet<T>,
    ) -> HashMap<AtomicProposition, IntervalSet<T>> {
        let mut intervals = self.extract_rec(self.formula, &Rc::new(holds_in)).0;
        intervals.retain(|_, i| !i.is_empty());
        intervals
    }

    fn extract_rec(
        &mut self,
        formula: &'a NNFFormula<T>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        // Check the cache for the current parameters
        let key = (formula, Rc::clone(holds_in));
        if self.cache.contains_key(&key) {
            println!("Cache hit: {:?}", key);
            return self.cache.get(&key).unwrap().clone();
        }

        let result = match formula {
            NNFFormula::True => NecessaryIntervals::default(),
            NNFFormula::False => self.extract_false(holds_in),
            NNFFormula::AP(ap) => self.extract_ap(ap, holds_in),
            NNFFormula::And(subs) => self.extract_and(subs, holds_in),
            NNFFormula::Or(subs) => self.extract_or(subs, holds_in),
            // Finally
            NNFFormula::Until(lhs, int, rhs) if **lhs == NNFFormula::True => {
                self.extract_finally(rhs, int, holds_in)
            }
            // Globally
            NNFFormula::Release(lhs, int, rhs) if **lhs == NNFFormula::False => {
                self.extract_globally(rhs, int, holds_in)
            }
            NNFFormula::Until(lhs, int, rhs) => self.extract_until(lhs, int, rhs, holds_in),
            NNFFormula::Release(lhs, int, rhs) => self.extract_release(lhs, int, rhs, holds_in),
        };

        // Update cache
        self.cache.insert(key, result.clone());
        result
    }

    fn extract_false(&self, holds_in: &Rc<IntervalSet<T>>) -> NecessaryIntervals<T> {
        NecessaryIntervals(
            self.formula
                .collect_aps()
                .into_iter()
                .map(|ap| (ap, holds_in.as_ref().clone()))
                .collect(),
        )
    }

    fn extract_ap(
        &self,
        ap: &AtomicProposition,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        NecessaryIntervals(HashMap::from_iter([(
            ap.clone(),
            holds_in.as_ref().clone(),
        )]))
    }

    fn extract_and(
        &mut self,
        subs: &'a BTreeSet<NNFFormula<T>>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        subs.iter()
            .map(|f| self.extract_rec(f, holds_in))
            .reduce(NecessaryIntervals::union)
            .unwrap_or_default()
    }

    fn extract_or(
        &mut self,
        subs: &'a BTreeSet<NNFFormula<T>>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        // Look at all subsets (and their complements) of the disjunction subformulas
        let subsets_with_rests = subs.iter().powerset().map(|set| {
            let rest = subs.iter().filter(|f| !set.contains(f)).collect_vec();
            (set, rest)
        });

        subsets_with_rests
            .filter_map(|(subset, rest)| {
                if subset.is_empty() {
                    return None;
                }

                // For each subset, find the intervals where its complement cannot hold
                let rest_cannot_hold = rest
                    .iter()
                    .map(|f| self.get_cannot(f))
                    .reduce(|acc: IntervalSet<T>, e| acc.intersect(&e))
                    .unwrap_or_else(|| Interval::unbounded(T::zero()).into());

                // At least one formula in the subset must hold, where the rest cannot hold
                let subset_holds_in = Rc::new(holds_in.intersect(&rest_cannot_hold));

                // If the subset does not have to hold anywhere, we won't get any new information
                if subset_holds_in.is_empty() {
                    return None;
                }

                // Find the necessary intervals for each formula in the subset
                // We obtain the necessary intervals for the subset by forming the intersecting,
                // since at least one formula in the subset must hold
                subset
                    .iter()
                    .map(|f| self.extract_rec(f, &subset_holds_in))
                    .reduce(NecessaryIntervals::intersect)
            })
            .reduce(NecessaryIntervals::union)
            .unwrap_or_default()
    }

    fn extract_finally(
        &mut self,
        sub: &'a NNFFormula<T>,
        interval: &Interval<T>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        // Check whether the finally is actually just a next
        if matches!(interval, Interval::Bounded { lb, ub } if lb == ub) {
            return self.extract_globally(sub, interval, holds_in);
        }

        holds_in
            .get_intervals()
            .iter()
            .map(|holds_in_interval| {
                // Analyze subformula as if it had to hold at 0 only
                // For this we need to contract the knowledge
                let shift = *interval + *holds_in_interval;
                self.knowledge_provider.contract(&shift);
                let necessary = self.extract_rec(
                    sub,
                    &Rc::from(IntervalSet::from(Interval::singleton(T::zero()))),
                );
                self.knowledge_provider.uncontract(&shift);

                // We need to shift the necessary intervals back to the original 0 point
                necessary
                    .minkowski_sum_intersection(interval)
                    .minkowski_sum(holds_in_interval)
            })
            .reduce(NecessaryIntervals::union)
            .unwrap_or_default()
    }

    fn extract_globally(
        &mut self,
        sub: &'a NNFFormula<T>,
        interval: &Interval<T>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        let sub_holds_in = Rc::new(holds_in.minkowski_sum(interval));
        self.extract_rec(sub, &sub_holds_in)
    }

    fn extract_until(
        &mut self,
        lhs: &'a NNFFormula<T>,
        interval: &Interval<T>,
        rhs: &'a NNFFormula<T>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        match interval {
            Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => {
                let rhs_cannot = self.get_cannot(rhs);
                let necessary_from_lhs = holds_in
                    .get_intervals()
                    .iter()
                    .map(|holds_in_interval| {
                        // We want to contract the holds_in_interval to the point 0, so we need to do the same to the knowledge
                        let contracted_rhs_cannot = rhs_cannot
                            .minkowski_difference(holds_in_interval)
                            .largest_contiguous_interval_with(*lb);
                        // MLTL semantics, so lhs does not need to hold in [0, lb - 1]
                        let lhs_must = contracted_rhs_cannot.intersect(interval);
                        let lhs_holds_in =
                            Rc::new(holds_in_interval.minkowski_sum(lhs_must).into());
                        self.extract_rec(lhs, &lhs_holds_in)
                    })
                    .reduce(NecessaryIntervals::union)
                    .unwrap_or_default();
                let necessary_from_rhs = self.extract_finally(rhs, interval, holds_in);
                necessary_from_lhs.union(necessary_from_rhs)
            }
            // Until with empty interval is equivalent to false
            Interval::Empty => self.extract_false(holds_in),
        }
    }

    fn extract_release(
        &mut self,
        lhs: &'a NNFFormula<T>,
        interval: &Interval<T>,
        rhs: &'a NNFFormula<T>,
        holds_in: &Rc<IntervalSet<T>>,
    ) -> NecessaryIntervals<T> {
        match interval {
            Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => {
                let lhs_cannot = self.get_cannot(lhs);
                holds_in
                    .get_intervals()
                    .iter()
                    .map(|holds_in_interval| {
                        // We want to contract the holds_in_interval to the point 0, so we need to do the same to the knowledge
                        let contracted_lhs_cannot = lhs_cannot
                            .minkowski_difference(holds_in_interval)
                            .largest_contiguous_interval_with(*lb);
                        // lhs must hold strictly before to trigger release so we can extend the interval by 1
                        let extended_lhs_cannot = match contracted_lhs_cannot {
                            Interval::Empty => Interval::singleton(*lb),
                            _ => contracted_lhs_cannot + Interval::bounded(T::zero(), T::one()),
                        };
                        // MLTL semantics, so release is not triggered when lhs hold in [0, lb - 1]
                        let rhs_must = extended_lhs_cannot.intersect(interval);
                        let rhs_holds_in =
                            Rc::new(holds_in_interval.minkowski_sum(rhs_must).into());
                        self.extract_rec(rhs, &rhs_holds_in)
                    })
                    .reduce(NecessaryIntervals::union)
                    .unwrap_or_default()
            }
            // Release with empty interval is equivalent to true
            Interval::Empty => NecessaryIntervals::default(),
        }
    }

    fn get_cannot(&self, formula: &NNFFormula<T>) -> IntervalSet<T> {
        self.knowledge_provider
            .get_cannot(formula)
            .expect("knowledge provider should contain knowledge for all subformulas")
    }
}

trait Merge<T> {
    fn merge<F>(&mut self, other: Self, f: F)
    where
        F: Fn(T, T) -> T;
}

impl<K: Eq + std::hash::Hash + Clone, V: Default> Merge<V> for HashMap<K, V> {
    fn merge<F>(&mut self, mut other: Self, f: F)
    where
        F: Fn(V, V) -> V,
    {
        let keys: HashSet<_> = self.keys().chain(other.keys()).cloned().collect();
        for k in keys {
            let s = self.remove(&k).unwrap_or_default();
            let o = other.remove(&k).unwrap_or_default();
            self.insert(k, f(s, o));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser::mltl_parser, signals::signal::Signal, trace_parser::trace_parser};

    use super::*;

    #[test]
    fn test_extract() {
        let phi = mltl_parser::formula("(a & b) | (a & c)")
            .expect("Syntax is correct")
            .into();
        let a_signal = Signal::uniform(Kleene::Unknown);
        let b_signal = Signal::indicator(&Interval::singleton(1), Kleene::False, Kleene::Unknown);
        let c_signal = Signal::indicator(&Interval::singleton(2), Kleene::False, Kleene::Unknown);
        let trace = Trace::from(HashMap::from_iter([
            (Rc::from("a"), a_signal),
            (Rc::from("b"), b_signal),
            (Rc::from("c"), c_signal),
        ]));
        let intervals =
            NecessaryIntervalExtractor::new(&phi, &trace).extract(Interval::bounded(0, 2).into());
        let expected = HashMap::from([
            (
                AtomicProposition {
                    name: Rc::from("a"),
                    negated: false,
                },
                Interval::bounded(0, 2).into(),
            ),
            (
                AtomicProposition {
                    name: Rc::from("b"),
                    negated: false,
                },
                Interval::singleton(2).into(),
            ),
            (
                AtomicProposition {
                    name: Rc::from("c"),
                    negated: false,
                },
                Interval::singleton(1).into(),
            ),
        ]);
        assert_eq!(intervals, expected);
    }

    #[test]
    fn test_ri5() {
        let ri5: NNFFormula<_> = mltl_parser::formula(include_str!("../ri5.txt"))
            .expect("Syntax is correct")
            .into();
        // let ri5_naive: NNFFormula<_> = mltl_parser::formula(include_str!("../ri5_naive.txt"))
        //     .expect("Syntax is correct")
        //     .into();
        // println!("{}", ri5);
        let trace =
            trace_parser::trace(include_str!("../trace_ri5.txt")).expect("Syntax is correct");
        let now = std::time::Instant::now();
        let mut extractor = NecessaryIntervalExtractor::new(&ri5, &trace);
        let mut intervals = extractor.extract(Interval::singleton(0).into());
        println!("{:.2?}", now.elapsed());
        intervals.retain(|_, i| !i.is_empty());
        // dbg!(extractor.knowledge.satisfaction_signals().values());
        dbg!(&intervals);
    }

    #[test]
    fn test_rg1() {
        let rg1: NNFFormula<_> = mltl_parser::formula(include_str!("../rg1.txt"))
            .expect("Syntax is correct")
            .into();
        let rg1_naive: NNFFormula<_> = mltl_parser::formula(include_str!("../rg1_naive.txt"))
            .expect("Syntax is correct")
            .into();
        let trace =
            trace_parser::trace(include_str!("../trace_rg1.txt")).expect("Syntax is correct");
        dbg!(&rg1);
        let mut extractor = NecessaryIntervalExtractor::new(&rg1_naive, &trace);
        let mut intervals = extractor.extract(Interval::singleton(0).into());
        intervals.retain(|_, i| !i.is_empty());
        let mut sat_sigs = extractor
            .knowledge_provider
            .knowledge
            .satisfaction_signals()
            .clone();
        sat_sigs.retain(|_, sig| sig != &Signal::uniform(Kleene::Unknown));
        dbg!(&sat_sigs);
        dbg!(&intervals);
    }

    #[test]
    fn test_iteration() {
        let phi: NNFFormula<_> = mltl_parser::formula("(G[0, 5] a) & (G[0, 10] a -> b)")
            .expect("Syntax is correct")
            .into();
        let mut trace = Trace::from(
            phi.collect_aps()
                .into_iter()
                .map(|ap| (ap.name, Signal::uniform(Kleene::Unknown)))
                .collect(),
        );
        let mut intervals = HashMap::new();
        loop {
            let mut extractor = NecessaryIntervalExtractor::new(&phi, &trace);
            let new_intervals = extractor.extract(Interval::singleton(0).into());
            dbg!(&new_intervals);
            println!("========================================");
            if new_intervals == intervals {
                intervals = new_intervals;
                break;
            }
            new_intervals.iter().for_each(|(ap, i)| {
                if ap.negated {
                    trace.set_ap(Rc::clone(&ap.name), i, Kleene::False);
                } else {
                    trace.set_ap(Rc::clone(&ap.name), i, Kleene::True);
                }
            });
            intervals = new_intervals;
        }
        println!("Final===================================");
        dbg!(&intervals);
    }

    #[test]
    fn test_finally() {
        let phi: NNFFormula<_> = mltl_parser::formula("F[0, 1] G[0, 4] a")
            .expect("Syntax is correct")
            .into();
        let trace = Trace::from(
            phi.collect_aps()
                .into_iter()
                .map(|ap| (ap.name, Signal::uniform(Kleene::Unknown)))
                .collect(),
        );
        let mut extractor = NecessaryIntervalExtractor::new(&phi, &trace);
        let intervals = extractor.extract(Interval::singleton(0).into());
        dbg!(&intervals);
    }
}
