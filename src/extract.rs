use std::{
    collections::{HashMap, HashSet},
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
}

type ExtractionCache<'a, T> =
    HashMap<(&'a NNFFormula<T>, Rc<IntervalSet<T>>), NecessaryIntervals<T>>;
pub struct NecessaryIntervalExtractor<'a, T> {
    formula: &'a NNFFormula<T>,
    knowledge: Monitor<'a, T, Kleene>,
    cache: ExtractionCache<'a, T>,
}

impl<'a, T: Integer + Unsigned + Copy + Hash + SaturatingSub + std::fmt::Debug>
    NecessaryIntervalExtractor<'a, T>
{
    pub fn new(formula: &'a NNFFormula<T>, trace: &Trace<T, Kleene>) -> Self {
        let knowledge = Monitor::new::<KleeneMonitorSignal<_>>(formula, trace);
        NecessaryIntervalExtractor {
            formula,
            knowledge,
            cache: HashMap::new(),
        }
    }

    pub fn extract(
        &mut self,
        holds_in: IntervalSet<T>,
    ) -> HashMap<AtomicProposition, IntervalSet<T>> {
        self.extract_rec(self.formula, &Rc::new(holds_in)).0
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
            NNFFormula::False => NecessaryIntervals(
                formula
                    .collect_aps()
                    .into_iter()
                    .map(|ap| (ap, holds_in.as_ref().clone()))
                    .collect(),
            ),
            NNFFormula::AP(ap) => NecessaryIntervals(HashMap::from_iter([(
                ap.clone(),
                holds_in.as_ref().clone(),
            )])),
            NNFFormula::And(subs) => subs
                .iter()
                .map(|f| self.extract_rec(f, holds_in))
                .reduce(NecessaryIntervals::union)
                .unwrap_or_default(),
            NNFFormula::Or(subs) => {
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
                            .map(|f| {
                                IntervalSet::from_iter(
                                    self.knowledge
                                        .satisfaction_signals()
                                        .get(f)
                                        .expect("knowledge should contain all subformulas")
                                        .intervals_where_eq(&Kleene::False),
                                )
                            })
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
            _ => todo!(),
        };

        // Update cache
        self.cache.insert(key, result.clone());
        result
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
    use std::rc::Rc;

    use crate::{parser::mltl_parser, sets::interval::Interval, signals::signal::Signal};

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
}
