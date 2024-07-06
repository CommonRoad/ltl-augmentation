use std::{collections::BTreeSet, ops::Add};

use itertools::Itertools;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Interval {
    Range(u32, u32),
    Empty,
}

impl Interval {
    pub fn empty() -> Interval {
        Interval::Empty
    }

    pub fn from_endpoints(start: u32, end: u32) -> Interval {
        if start > end {
            Interval::Empty
        } else {
            Interval::Range(start, end)
        }
    }

    pub fn from_signed_endpoints(start: i32, end: i32) -> Interval {
        if end < 0 || start > end {
            Interval::Empty
        } else {
            let start = start.max(0) as u32;
            let end = end as u32;
            Interval::Range(start, end)
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }

    pub fn intersect(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Range(start1, end1), Interval::Range(start2, end2)) => {
                let start = start1.max(start2);
                let end = end1.min(end2);
                Interval::from_endpoints(*start, *end)
            }
            _ => Interval::Empty,
        }
    }

    pub fn difference(&self, other: &Interval) -> (Interval, Interval) {
        match (self, other) {
            (Interval::Range(start1, end1), Interval::Range(start2, end2)) => {
                if end1 < start2 {
                    (*self, Interval::empty())
                } else if start1 > end2 {
                    (Interval::empty(), *self)
                } else {
                    (
                        Interval::from_endpoints(*start1, start2 - 1),
                        Interval::from_endpoints(end2 + 1, *end1),
                    )
                }
            }
            _ => (*self, Interval::empty()),
        }
    }

    pub fn union_all(intervals: impl IntoIterator<Item = Interval>) -> Vec<Interval> {
        let mut sorted_non_empty = intervals
            .into_iter()
            .filter_map(|i| match i {
                Interval::Range(start, end) => Some((start, end)),
                Interval::Empty => None,
            })
            .sorted_unstable();
        let mut result = Vec::new();
        if let Some(mut current) = sorted_non_empty.next() {
            for (start, end) in sorted_non_empty {
                if start <= current.1 + 1 {
                    current.1 = current.1.max(end);
                } else {
                    result.push(Interval::Range(current.0, current.1));
                    current = (start, end);
                }
            }
            result.push(Interval::Range(current.0, current.1));
        }
        result
    }

    pub fn merge<T: Clone + std::cmp::Eq>(
        intervals: Vec<(Interval, T)>,
    ) -> Vec<(Interval, Vec<T>)> {
        // Create a list of events, each with a time, a boolean indicating if it's an entry or exit event, and the value
        // A value becomes active at the time of an entry event and inactive at the time of an exit event
        // For each interval, we generate an entry event at the lower endpoint and an exit event at the upper endpoint
        let mut events: Vec<_> = intervals
            .into_iter()
            .filter(|(int, _)| !int.is_empty())
            .flat_map(|(int, val)| match int {
                Interval::Range(start, end) => {
                    vec![(start, true, val.clone()), (end, false, val)]
                }
                Interval::Empty => unreachable!(),
            })
            .collect();
        // Sort by time ascending (entry events come before exit events at the same time)
        events.sort_unstable_by_key(|(time, is_entry, _)| (*time, *is_entry));

        let mut merged = Vec::new();
        let mut active = Vec::new();
        let mut start = 0_u32;
        for (time, is_entry, val) in events {
            // Entry events complete the interval until time - 1 (because it becomes active at time)
            // Exit events complete the interval until time (because it becomes inactive at time)
            // Since we process entry events first, we correctly get unitary intervals if both entries and exits happen at the same time
            // Entry events at time 0 never complete an interval
            if !is_entry || time > 0 {
                let end = if is_entry { time - 1 } else { time };
                if end >= start && !active.is_empty() {
                    // Create a new interval with all active values
                    merged.push((Interval::from_endpoints(start, end), active.clone()));
                }
                // The next interval always starts one step after the one we just completed
                start = end + 1;
            }

            // Activate or deactivate the value
            if is_entry {
                active.push(val);
            } else {
                active.retain(|v| v != &val);
            }
        }

        merged
    }
}

impl Add for Interval {
    type Output = Interval;

    fn add(self, rhs: Interval) -> Interval {
        match (self, rhs) {
            (Interval::Range(start1, end1), Interval::Range(start2, end2)) => {
                Interval::Range(start1 + start2, end1 + end2)
            }
            _ => Interval::Empty,
        }
    }
}

pub struct IntervalSet {
    bounds: BTreeSet<(u32, bool)>,
}

impl IntervalSet {
    pub fn new() -> IntervalSet {
        IntervalSet {
            bounds: BTreeSet::new(),
        }
    }

    pub fn add(&mut self, interval: &Interval) {
        match interval {
            Interval::Range(start, end) => {
                self.set(*start, end + 1, true);
            }
            Interval::Empty => (),
        }
    }

    pub fn remove(&mut self, interval: &Interval) {
        match interval {
            Interval::Range(start, end) => {
                self.set(*start, end + 1, false);
            }
            Interval::Empty => (),
        }
    }

    fn set(&mut self, lb: u32, ub: u32, included: bool) {
        let lb = (lb, included);
        let ub = (ub, !included);

        // Remove everything between lb and ub
        self.bounds.retain(|x| x < &lb || x > &ub);

        // Find the next smaller bound
        let left = self.bounds.range(..lb).next_back().copied();
        match left {
            // Opening bound: New interval is extended to the left, so do nothing
            Some((_, opening)) if opening == included => (),
            // Closing bound exactly at lb: New interval connects to the left, so remove the separating bound
            Some(bound @ (x, opening)) if opening != included && x == lb.0 => {
                self.bounds.remove(&bound);
            }
            // Otherwise: There is a gap between new interval and left, so insert the bound
            _ => {
                self.bounds.insert(lb);
            }
        };

        let right = self.bounds.range(ub..).next().copied();
        match right {
            // Closing bound: New interval is extended to the right, so do nothing
            Some((_, opening)) if opening != included => (),
            // Opening bound exactly at ub: New interval connects to the right, so remove the separating bound
            Some(bound @ (x, opening)) if opening == included && x == ub.0 => {
                self.bounds.remove(&bound);
            }
            // Otherwise: There is a gap between new interval and right, so insert the bound
            _ => {
                self.bounds.insert(ub);
            }
        };
    }

    pub fn get_intervals(&self) -> Vec<Interval> {
        self.bounds
            .iter()
            .chunks(2)
            .into_iter()
            .map(|chunk| {
                let ((start, _), (end, _)) = chunk
                    .collect_tuple()
                    .expect("Number of bounds is always even");
                Interval::from_endpoints(*start, end - 1)
            })
            .collect()
    }
}

impl Default for IntervalSet {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Interval> for IntervalSet {
    fn from(interval: Interval) -> IntervalSet {
        match interval {
            Interval::Empty => IntervalSet::new(),
            Interval::Range(start, end) => IntervalSet {
                bounds: BTreeSet::from([(start, true), (end + 1, false)]),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_union_all() {
        let intervals = [
            Interval::from_endpoints(1, 3),
            Interval::from_endpoints(1, 4),
            Interval::from_endpoints(8, 10),
            Interval::from_endpoints(5, 6),
            Interval::from_endpoints(9, 11),
            Interval::from_endpoints(20, 100),
        ];
        let union = Interval::union_all(intervals);
        assert_eq!(
            union,
            vec![
                Interval::from_endpoints(1, 6),
                Interval::from_endpoints(8, 11),
                Interval::from_endpoints(20, 100)
            ]
        );
    }

    #[test]
    fn test_merge() {
        let intervals = vec![
            (Interval::from_endpoints(1, 3), 1),
            (Interval::from_endpoints(2, 4), 2),
            (Interval::from_endpoints(5, 6), 3),
        ];

        let merged = Interval::merge(intervals);

        assert_eq!(
            merged.into_iter().collect::<HashSet<_>>(),
            vec![
                (Interval::from_endpoints(1, 1), vec![1]),
                (Interval::from_endpoints(2, 3), vec![1, 2]),
                (Interval::from_endpoints(4, 4), vec![2]),
                (Interval::from_endpoints(5, 6), vec![3]),
            ]
            .into_iter()
            .collect::<HashSet<_>>()
        );
    }

    #[test]
    fn test_interval_set() {
        let mut is = IntervalSet::new();
        assert!(is.get_intervals().is_empty());

        let i1 = Interval::from_endpoints(0, 10);
        is.add(&i1);
        assert_eq!(is.get_intervals(), vec![i1]);

        is.add(&Interval::from_endpoints(3, 4));
        assert_eq!(is.get_intervals(), vec![i1]);

        let i2 = Interval::from_endpoints(20, 30);
        is.add(&i2);
        assert_eq!(is.get_intervals(), vec![i1, i2]);

        is.add(&Interval::from_endpoints(11, 19));
        assert_eq!(is.get_intervals(), vec![Interval::from_endpoints(0, 30)]);

        is.remove(&Interval::from_endpoints(11, 19));
        assert_eq!(is.get_intervals(), vec![i1, i2]);

        is.add(&Interval::from_endpoints(30, 40));
        assert_eq!(
            is.get_intervals(),
            vec![i1, Interval::from_endpoints(20, 40)]
        );
    }
}
