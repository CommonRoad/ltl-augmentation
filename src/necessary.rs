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

pub fn collect_aps(nnf: &NNFFormula) -> HashSet<AtomicProposition> {
    match nnf {
        NNFFormula::True | NNFFormula::False => HashSet::new(),
        NNFFormula::AP(name, negated) => HashSet::from([AtomicProposition {
            ap_name: Rc::from(name.as_str()),
            negated: *negated,
        }]),
        NNFFormula::And(subs) | NNFFormula::Or(subs) => subs
            .iter()
            .map(collect_aps)
            .reduce(|mut acc, e| {
                acc.extend(e);
                acc
            })
            .unwrap_or_default(),
        NNFFormula::Until(lhs, _, rhs) | NNFFormula::Release(lhs, _, rhs) => {
            let mut set = collect_aps(lhs);
            set.extend(collect_aps(rhs));
            set
        }
    }
}

pub fn necessary_intervals(nnf: &NNFFormula) -> HashMap<AtomicProposition, IntervalSet> {
    let mut intervals = collect_necessary_intervals(nnf, &collect_aps(nnf));
    intervals.retain(|_, v| !v.is_empty());
    intervals
}

fn collect_necessary_intervals(
    nnf: &NNFFormula,
    all_aps: &HashSet<AtomicProposition>,
) -> HashMap<AtomicProposition, IntervalSet> {
    match nnf {
        NNFFormula::True => HashMap::new(), // True requires nothing
        NNFFormula::False => all_aps
            .iter()
            .map(|ap| (ap.clone(), Interval::from_endpoints(0, 0).into()))
            .collect(), // False requires everything
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
            .map(|f| collect_necessary_intervals(f, all_aps))
            .reduce(|mut acc, e| {
                acc.merge(e, IntervalSet::union);
                acc
            })
            .unwrap_or_default(),
        NNFFormula::Or(subs) => subs
            .iter()
            .map(|f| collect_necessary_intervals(f, all_aps))
            .reduce(|mut acc, e| {
                acc.merge(e, IntervalSet::intersect);
                acc
            })
            .unwrap_or_default(),
        NNFFormula::Until(_, shift @ Interval::Range(lb, ub), rhs)
        | NNFFormula::Release(_, shift @ Interval::Range(lb, ub), rhs)
            if lb == ub =>
        {
            let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
            rhs_intervals
                .into_iter()
                .map(|(k, v)| (k, v.minkowski_sum(shift)))
                .collect()
        }
        NNFFormula::Until(lhs, int, rhs) => match int {
            Interval::Empty => panic!("Malformed formula: Empty interval in Until"),
            Interval::Range(lb, _) => {
                let mut lhs_intervals = collect_necessary_intervals(lhs, all_aps);
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                let shift = Interval::from_endpoints(*lb, *lb);
                lhs_intervals.merge(rhs_intervals, |lhs, rhs| {
                    lhs.minkowski_sum(&shift)
                        .intersect(rhs.minkowski_sum(&shift))
                });
                lhs_intervals
            }
        },
        NNFFormula::Release(lhs, int, rhs) if **lhs == NNFFormula::False => match int {
            Interval::Empty => panic!("Malformed formula: Empty interval in Release"),
            shift @ Interval::Range(..) => {
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                rhs_intervals
                    .into_iter()
                    .map(|(k, v)| (k, v.minkowski_sum(shift)))
                    .collect()
            }
        },
        NNFFormula::Release(lhs, int, rhs) => match int {
            Interval::Empty => panic!("Malformed formula: Empty interval in Until"),
            Interval::Range(lb, _) => {
                let mut lhs_intervals = collect_necessary_intervals(lhs, all_aps);
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                let shift_lb = Interval::from_endpoints(*lb, *lb);
                let shift_suc_lb = Interval::from_endpoints(lb + 1, lb + 1);
                lhs_intervals.merge(rhs_intervals, |lhs, rhs| {
                    // Rhs must hold at lb
                    rhs.clone().minkowski_sum(&shift_lb).union(
                        // Lhs or rhs must hold at lb + 1
                        lhs.minkowski_sum(&shift_suc_lb)
                            .intersect(rhs.minkowski_sum(&shift_suc_lb)),
                    )
                });
                lhs_intervals
            }
        },
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

    #[test]
    fn test_necessary_intervals2() {
        let phi = mltl_parser::formula("(a & b) U[1, 2] (a & c)")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([(
            AtomicProposition {
                ap_name: Rc::from("a"),
                negated: false,
            },
            Interval::from_endpoints(1, 1).into(),
        )]);
        assert_eq!(intervals, expected);
    }

    #[test]
    fn test_necessary_intervals3() {
        let phi = mltl_parser::formula("G[0, 10] (a & b)")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([
            (
                AtomicProposition {
                    ap_name: Rc::from("a"),
                    negated: false,
                },
                Interval::from_endpoints(0, 10).into(),
            ),
            (
                AtomicProposition {
                    ap_name: Rc::from("b"),
                    negated: false,
                },
                Interval::from_endpoints(0, 10).into(),
            ),
        ]);
        assert_eq!(intervals, expected);
    }

    #[test]
    fn test_necessary_intervals4() {
        let phi = mltl_parser::formula("(a & c) R[5, 10] (a & b)")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([
            (
                AtomicProposition {
                    ap_name: Rc::from("a"),
                    negated: false,
                },
                Interval::from_endpoints(5, 6).into(),
            ),
            (
                AtomicProposition {
                    ap_name: Rc::from("b"),
                    negated: false,
                },
                Interval::from_endpoints(5, 5).into(),
            ),
        ]);
        assert_eq!(intervals, expected);
    }

    #[test]
    fn test_necessary_intervals5() {
        let phi = mltl_parser::formula("a U[2, 2] b")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([(
            AtomicProposition {
                ap_name: Rc::from("b"),
                negated: false,
            },
            Interval::from_endpoints(2, 2).into(),
        )]);
        assert_eq!(intervals, expected);
    }

    #[test]
    fn test_necessary_intervals6() {
        let phi = mltl_parser::formula("(G[3, 9] a & c) | (G[1, 2] G[1, 2] b & c)")
            .expect("Syntax is correct")
            .into();
        let intervals = necessary_intervals(&phi);
        let expected = HashMap::from([(
            AtomicProposition {
                ap_name: Rc::from("c"),
                negated: false,
            },
            Interval::from_endpoints(3, 4).into(),
        )]);
        assert_eq!(intervals, expected);
    }
}
