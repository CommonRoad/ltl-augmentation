use std::{collections::BTreeSet, os::unix::fs::OpenOptionsExt};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::sets::interval::Interval;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalSet<T> {
    bounds: BTreeSet<(T, bool)>,
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> IntervalSet<T> {
    pub fn new() -> Self {
        IntervalSet {
            bounds: BTreeSet::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bounds.is_empty()
    }

    pub fn add(&mut self, interval: &Interval<T>) {
        match interval {
            Interval::Bounded { lb, ub } => {
                self.set(*lb, *ub + T::one(), true);
            }
            Interval::Unbounded { lb } => {
                self.set_unbounded(*lb, true);
            }
            Interval::Empty => (),
        }
    }

    pub fn remove(&mut self, interval: &Interval<T>) {
        match interval {
            Interval::Bounded { lb, ub } => {
                self.set(*lb, *ub + T::one(), false);
            }
            Interval::Unbounded { lb } => {
                self.set_unbounded(*lb, false);
            }
            Interval::Empty => (),
        }
    }

    fn set(&mut self, lb: T, ub: T, included: bool) {
        let lb = (lb, included);
        let ub = (ub, !included);

        // Remove everything between lb and ub
        self.bounds.retain(|x| x < &lb || x > &ub);

        self.add_left_bound(lb);
        self.add_right_bound(ub);
    }

    fn set_unbounded(&mut self, lb: T, included: bool) {
        let lb = (lb, included);

        // Remove everything above lb
        self.bounds.retain(|x| x < &lb);

        self.add_left_bound(lb);
    }

    fn add_left_bound(&mut self, lb: (T, bool)) {
        let left = self.bounds.range(..lb).next_back().copied();
        self.add_bound(lb, left);
    }

    fn add_right_bound(&mut self, ub: (T, bool)) {
        let right = self.bounds.range(ub..).next().copied();
        self.add_bound(ub, right);
    }

    fn add_bound(&mut self, bound: (T, bool), adjacent: Option<(T, bool)>) {
        match adjacent {
            // Opening of adjacent bound matches the new bound: New bound has no effect, so do nothing
            Some((_, opening)) if opening == bound.1 => (),
            // New bound adds inverse opening exactly at adjacent: We connect two intervals, so remove the separating bound
            Some(adj @ (x, opening)) if opening != bound.1 && x == bound.0 => {
                self.bounds.remove(&adj);
            }
            // Otherwise: The new bound does not interfere with the adjacent one, so add it
            _ => {
                self.bounds.insert(bound);
            }
        };
    }

    pub fn union(self, other: Self) -> Self {
        // TODO: Adjust for unbounded intervals
        let bounds =
            IntervalSet::normalize_bounds(self.bounds.into_iter().merge(other.bounds)).collect();
        IntervalSet { bounds }
    }

    pub fn intersect(self, other: Self) -> Self {
        let mut self_active = false;
        let mut other_active = false;

        let mut bounds = BTreeSet::new();
        for ((time, opening), from_self) in self
            .bounds
            .into_iter()
            .map(|bound| (bound, true))
            .merge(other.bounds.into_iter().map(|bound| (bound, false)))
        {
            // If both sets are active, then an opening bound is relevant to the intersection
            // If both sets were active, then a closing bound is relevant to the intersection
            // Thus, we first process activations, then potentially add the bound, and then process deactivations
            if opening {
                if from_self {
                    self_active = true;
                } else {
                    other_active = true;
                }
            }
            if self_active && other_active {
                bounds.insert((time, opening));
            }
            if !opening {
                if from_self {
                    self_active = false;
                } else {
                    other_active = false;
                }
            }
        }

        IntervalSet { bounds }
    }

    pub fn minkowski_sum(self, interval: &Interval<T>) -> Self {
        match interval {
            Interval::Empty => IntervalSet::new(),
            Interval::Bounded { lb, ub } => {
                let bounds =
                    IntervalSet::normalize_bounds(self.bounds.into_iter().map(
                        |bound| match bound {
                            (x, true) => (x + *lb, true),
                            (x, false) => (x + *ub, false),
                        },
                    ))
                    .collect();
                IntervalSet { bounds }
            }
            Interval::Unbounded { lb } => {
                let bounds = self
                    .bounds
                    .into_iter()
                    .next()
                    .map(|bound| match bound {
                        (x, true) => (x + *lb, true),
                        (_, false) => unreachable!("The first bound must be an opening bound"),
                    })
                    .into_iter()
                    .collect();
                IntervalSet { bounds }
            }
        }
    }

    pub fn back_shift(self, interval: &Interval<T>) -> Self {
        match interval {
            Interval::Empty => IntervalSet::new(),
            Interval::Bounded { lb, ub } => {
                let bounds =
                    IntervalSet::normalize_bounds(self.bounds.into_iter().map(
                        |bound| match bound {
                            (x, true) => (x.saturating_sub(ub), true),
                            (x, false) => (x.saturating_sub(lb), false),
                        },
                    ))
                    .collect();
                IntervalSet { bounds }
            }
            Interval::Unbounded { lb } => {
                let bounds = self
                    .bounds
                    .into_iter()
                    .next_back()
                    .map(|bound| match bound {
                        (_, true) => (T::zero(), true),
                        (x, false) => (x.saturating_sub(lb), false),
                    })
                    .into_iter()
                    .collect();
                IntervalSet { bounds }
            }
        }
    }

    pub fn get_intervals(&self) -> Vec<Interval<T>> {
        self.bounds
            .iter()
            .chunks(2)
            .into_iter()
            .map(|chunk| {
                let chunk = chunk.collect_vec();
                match chunk.len() {
                    1 => Interval::unbounded(chunk[0].0),
                    2 => Interval::bounded(chunk[0].0, chunk[1].0.saturating_sub(&T::one())),
                    _ => unreachable!("Chunks must have length 1 or 2"),
                }
            })
            .collect()
    }

    fn normalize_bounds(
        bounds: impl Iterator<Item = (T, bool)>,
    ) -> impl Iterator<Item = (T, bool)> {
        bounds
            .map(Some)
            .coalesce(|bound1, bound2| match (bound1, bound2) {
                (Some((_, true)), Some((_, true))) => Ok(bound1), // Keep lowest bound for opens
                (Some((_, false)), Some((_, false))) => Ok(bound2), // Keep highest bound for closes
                (Some((a, false)), Some((b, true))) if a == b => Ok(None), // Eliminate open/close on same value
                (None, _) => Ok(bound2),                                   // None can be dropped
                _ => Err((bound1, bound2)),
            })
            .map(|option| option.expect("None must have been dropped by coalesce"))
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> Default for IntervalSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> From<Interval<T>> for IntervalSet<T> {
    fn from(interval: Interval<T>) -> Self {
        match interval {
            Interval::Empty => IntervalSet::new(),
            Interval::Bounded { lb, ub } => IntervalSet {
                bounds: BTreeSet::from([(lb, true), (ub + T::one(), false)]),
            },
            Interval::Unbounded { lb } => IntervalSet {
                bounds: BTreeSet::from([(lb, true)]),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_interval_set() {
        let mut is = IntervalSet::<u32>::new();
        assert!(is.get_intervals().is_empty());

        let i0 = Interval::bounded(1, 1);
        is.add(&i0);
        assert_eq!(is.get_intervals(), vec![i0]);

        let i1 = Interval::bounded(0, 10);
        is.add(&i1);
        assert_eq!(is.get_intervals(), vec![i1]);

        is.add(&Interval::bounded(3, 4));
        assert_eq!(is.get_intervals(), vec![i1]);

        let i2 = Interval::bounded(20, 30);
        is.add(&i2);
        assert_eq!(is.get_intervals(), vec![i1, i2]);

        is.add(&Interval::bounded(11, 19));
        assert_eq!(is.get_intervals(), vec![Interval::bounded(0, 30)]);

        is.remove(&Interval::bounded(11, 19));
        assert_eq!(is.get_intervals(), vec![i1, i2]);

        is.add(&Interval::bounded(30, 40));
        assert_eq!(is.get_intervals(), vec![i1, Interval::bounded(20, 40)]);
    }

    #[test]
    fn test_interval_set_union() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(9, 19);
        let i3 = Interval::bounded(20, 30);
        let i4 = Interval::bounded(50, 60);
        let i5 = Interval::bounded(70, 100);
        let i6 = Interval::bounded(80, 90);

        let mut is1 = IntervalSet::<u32>::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::<u32>::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.union(is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(0, 30), i4, i5]);
    }

    #[test]
    fn test_interval_set_union_unbounded() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(9, 19);
        let i3 = Interval::bounded(20, 30);
        let i4 = Interval::bounded(50, 60);
        let i5 = Interval::unbounded(70);
        let i6 = Interval::bounded(80, 90);

        let mut is1 = IntervalSet::<u32>::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::<u32>::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.union(is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(0, 30), i4, i5]);
    }

    #[test]
    fn test_interval_set_intersect() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(9, 19);
        let i3 = Interval::bounded(20, 30);
        let i4 = Interval::bounded(50, 60);
        let i5 = Interval::bounded(70, 100);
        let i6 = Interval::bounded(80, 90);

        let mut is1 = IntervalSet::<u32>::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::<u32>::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.intersect(is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(9, 10), i6]);
    }

    #[test]
    fn test_interval_set_intersect_singular() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(10, 20);

        let mut is1 = IntervalSet::<u32>::new();
        is1.add(&i1);

        let mut is2 = IntervalSet::<u32>::new();
        is2.add(&i2);

        let is = is1.intersect(is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(10, 10)]);
    }

    #[test]
    fn test_interval_set_intersect_unbounded() {
        let i1 = Interval::bounded(0, 6);
        let i2 = Interval::bounded(10, 20);
        let i3 = Interval::unbounded(5);

        let mut is1 = IntervalSet::<u32>::new();
        is1.add(&i1);
        is1.add(&i2);

        let mut is2 = IntervalSet::<u32>::new();
        is2.add(&i3);

        let is = is1.intersect(is2);
        assert_eq!(
            is.get_intervals(),
            vec![Interval::bounded(5, 6), Interval::bounded(10, 20)]
        );
    }

    #[test]
    fn test_interval_set_minkowski_sum() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(12, 20);

        let mut is = IntervalSet::<u32>::new();
        is.add(&i1);
        is.add(&i2);

        let res = is.minkowski_sum(&Interval::bounded(2, 3));
        assert_eq!(res.get_intervals(), vec![Interval::bounded(2, 23)]);
    }

    #[test]
    fn test_interval_set_back_shift() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(12, 20);

        let mut is = IntervalSet::<u32>::new();
        is.add(&i1);
        is.add(&i2);

        let res = is.back_shift(&Interval::bounded(2, 3));
        assert_eq!(res.get_intervals(), vec![Interval::bounded(0, 18)]);
    }
}
