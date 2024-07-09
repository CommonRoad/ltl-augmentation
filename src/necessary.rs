use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    sets::{interval::Interval, interval_set::IntervalSet},
};

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

pub fn necessary_intervals<T: Integer + Unsigned + Copy + Hash + SaturatingSub>(
    nnf: &NNFFormula<T>,
) -> HashMap<AtomicProposition, IntervalSet<T>> {
    let mut intervals = collect_necessary_intervals(nnf, &nnf.collect_aps());
    intervals.retain(|_, v| !v.is_empty());
    intervals
}

fn collect_necessary_intervals<T: Integer + Unsigned + Copy + Hash + SaturatingSub>(
    nnf: &NNFFormula<T>,
    all_aps: &HashSet<AtomicProposition>,
) -> HashMap<AtomicProposition, IntervalSet<T>> {
    match nnf {
        NNFFormula::True => HashMap::new(), // True requires nothing
        NNFFormula::False => all_aps
            .iter()
            .map(|ap| (ap.clone(), Interval::singleton(T::zero()).into()))
            .collect(), // False requires everything
        NNFFormula::AP(ap) => {
            HashMap::from_iter([(ap.clone(), Interval::singleton(T::zero()).into())])
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
        NNFFormula::Until(_, shift @ Interval::Bounded { lb, ub }, rhs)
        | NNFFormula::Release(_, shift @ Interval::Bounded { lb, ub }, rhs)
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
            Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => {
                let mut lhs_intervals = collect_necessary_intervals(lhs, all_aps);
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                let shift = Interval::singleton(*lb);
                lhs_intervals.merge(rhs_intervals, |lhs, rhs| {
                    lhs.minkowski_sum(&shift)
                        .intersect(rhs.minkowski_sum(&shift))
                });
                lhs_intervals
            }
        },
        NNFFormula::Release(lhs, int, rhs) if **lhs == NNFFormula::False => match int {
            Interval::Empty => panic!("Malformed formula: Empty interval in Release"),
            shift => {
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                rhs_intervals
                    .into_iter()
                    .map(|(k, v)| (k, v.minkowski_sum(shift)))
                    .collect()
            }
        },
        NNFFormula::Release(lhs, int, rhs) => match int {
            Interval::Empty => panic!("Malformed formula: Empty interval in Until"),
            Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => {
                let mut lhs_intervals = collect_necessary_intervals(lhs, all_aps);
                let rhs_intervals = collect_necessary_intervals(rhs, all_aps);
                let shift_lb = Interval::singleton(*lb);
                let shift_suc_lb = Interval::singleton(*lb + T::one());
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
    use std::rc::Rc;

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
                name: Rc::from("a"),
                negated: false,
            },
            Interval::singleton(0).into(),
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
                name: Rc::from("a"),
                negated: false,
            },
            Interval::singleton(1).into(),
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
                    name: Rc::from("a"),
                    negated: false,
                },
                Interval::bounded(0, 10).into(),
            ),
            (
                AtomicProposition {
                    name: Rc::from("b"),
                    negated: false,
                },
                Interval::bounded(0, 10).into(),
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
                    name: Rc::from("a"),
                    negated: false,
                },
                Interval::bounded(5, 6).into(),
            ),
            (
                AtomicProposition {
                    name: Rc::from("b"),
                    negated: false,
                },
                Interval::singleton(5).into(),
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
                name: Rc::from("b"),
                negated: false,
            },
            Interval::singleton(2).into(),
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
                name: Rc::from("c"),
                negated: false,
            },
            Interval::bounded(3, 4).into(),
        )]);
        assert_eq!(intervals, expected);
    }
}
