use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    formula::NNFFormula,
    interval::{Interval, IntervalSet},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AtomicProposition {
    pub ap_name: Rc<str>,
    pub negated: bool,
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

pub fn necessary_intervals(nnf: &NNFFormula) -> HashMap<AtomicProposition, IntervalSet> {
    let mut intervals = collect_necessary_intervals(nnf);
    intervals.retain(|_, v| !v.is_empty());
    intervals
}

fn collect_necessary_intervals(nnf: &NNFFormula) -> HashMap<AtomicProposition, IntervalSet> {
    match nnf {
        NNFFormula::AP(name, negated) => {
            let mut map = HashMap::new();
            map.insert(
                AtomicProposition {
                    ap_name: Rc::from(name.as_str()),
                    negated: *negated,
                },
                Interval::from_endpoints(0, 0).into(),
            );
            map
        }
        NNFFormula::And(subs) => subs
            .iter()
            .map(collect_necessary_intervals)
            .reduce(|mut acc, e| {
                acc.merge(e, IntervalSet::union);
                acc
            })
            .unwrap_or_default(),
        NNFFormula::Or(subs) => subs
            .iter()
            .map(collect_necessary_intervals)
            .reduce(|mut acc, e| {
                acc.merge(e, IntervalSet::intersect);
                acc
            })
            .unwrap_or_default(),
        _ => todo!(),
    }
}

#[cfg(test)]
mod test {
    use crate::parser::mltl_parser;

    use super::*;

    #[test]
    fn test_necessary_intervals() {
        let phi = mltl_parser::formula("(a & b) | (a & c)")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([(
            AtomicProposition {
                ap_name: Rc::from("a"),
                negated: false,
            },
            Interval::from_endpoints(0, 0).into(),
        )]);
        assert_eq!(intervals, expected);
    }
}
