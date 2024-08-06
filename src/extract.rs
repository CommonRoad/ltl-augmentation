use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    monitoring::monitor::Monitor,
    sets::interval_set::IntervalSet,
    signals::truth_values::Kleene,
};

#[derive(Debug)]
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

pub fn extract<T>(
    knowledge: &Monitor<T, Kleene>,
    holds_in: &IntervalSet<T>,
) -> HashMap<AtomicProposition, IntervalSet<T>>
where
    T: Integer + Unsigned + Copy + Hash + SaturatingSub,
{
    extract_rec(knowledge.root(), knowledge, holds_in).0
}

fn extract_rec<T>(
    formula: &NNFFormula<T>,
    knowledge: &Monitor<T, Kleene>,
    holds_in: &IntervalSet<T>,
) -> NecessaryIntervals<T>
where
    T: Integer + Unsigned + Copy + Hash + SaturatingSub,
{
    match formula {
        NNFFormula::True => NecessaryIntervals::default(),
        NNFFormula::False => NecessaryIntervals(
            formula
                .collect_aps()
                .into_iter()
                .map(|ap| (ap, holds_in.clone()))
                .collect(),
        ),
        NNFFormula::AP(ap) => {
            NecessaryIntervals(HashMap::from_iter([(ap.clone(), holds_in.clone())]))
        }
        NNFFormula::And(subs) => subs
            .iter()
            .map(|f| extract_rec(f, knowledge, holds_in))
            .reduce(NecessaryIntervals::union)
            .unwrap_or_default(),
        NNFFormula::Or(subs) => {
            let from_cannot = subs
                .iter()
                .map(|f| {
                    let others_cannot_hold = subs
                        .iter()
                        .filter(|&o| o != f)
                        .map(|o| {
                            IntervalSet::from_iter(
                                knowledge
                                    .satisfaction_signals()
                                    .get(o)
                                    .expect("knowledge should contain all subformulas")
                                    .intervals_where_eq(&Kleene::False),
                            )
                        })
                        .reduce(|acc, e| acc.intersect(&e))
                        .unwrap_or_default();
                    extract_rec(f, knowledge, &others_cannot_hold)
                })
                .reduce(NecessaryIntervals::union)
                .unwrap_or_default();
            let from_all = subs
                .iter()
                .map(|f| extract_rec(f, knowledge, holds_in))
                .reduce(NecessaryIntervals::intersect)
                .unwrap_or_default();
            from_cannot.union(from_all)
        }
        _ => todo!(),
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

    use itertools::Itertools;

    use crate::{
        monitoring::kleene::KleeneMonitorSignal, parser::mltl_parser, sets::interval::Interval,
        signals::signal::Signal, trace::Trace,
    };

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
            ("a", a_signal),
            ("b", b_signal),
            ("c", c_signal),
        ]));
        let monitor = Monitor::new::<KleeneMonitorSignal<_>>(&phi, &trace);
        let intervals = extract(&monitor, &Interval::bounded(0, 2).into());
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
    fn test_ps() {
        let f = [NNFFormula::<u32>::True, NNFFormula::False];
        let v = f.iter().powerset().collect_vec();
    }
}
