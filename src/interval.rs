use std::ops::Add;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
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
        match self {
            Interval::Empty => true,
            _ => false,
        }
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
        let mut start = 0 as u32;
        for (time, is_entry, val) in events {
            // Entry events complete the interval until time - 1 (because it becomes active at time)
            // Exit events complete the interval until time (because it becomes inactive at time)
            // Since we process entry events first, we correctly get unitary intervals if both entries and exits happen at the same time
            let end = if is_entry { time - 1 } else { time };
            if end >= start && !active.is_empty() {
                // Create a new interval with all active values
                merged.push((Interval::from_endpoints(start, end), active.clone()));
            }
            // The next interval always starts one step after the one we just completed
            start = end + 1;

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

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test() {
        assert!(true > false);
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
}
