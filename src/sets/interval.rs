use num::{traits::SaturatingSub, Integer, Unsigned};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Interval<T> {
    Empty,
    Bounded { lb: T, ub: T },
    Unbounded { lb: T },
}

impl<T: Ord> Interval<T> {
    pub fn empty() -> Self {
        Interval::Empty
    }

    pub fn bounded(lb: T, ub: T) -> Self {
        if lb > ub {
            Interval::Empty
        } else {
            Interval::Bounded { lb, ub }
        }
    }

    pub fn unbounded(lb: T) -> Self {
        Interval::Unbounded { lb }
    }

    pub fn singleton(v: T) -> Self
    where
        T: Copy,
    {
        Interval::Bounded { lb: v, ub: v }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }

    pub fn intersect(&self, other: &Self) -> Self
    where
        T: Copy,
    {
        match (self, other) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (Interval::Bounded { lb: lb1, ub: ub1 }, Interval::Bounded { lb: lb2, ub: ub2 }) => {
                Interval::bounded(*lb1.max(lb2), *ub1.min(ub2))
            }
            (Interval::Bounded { lb: lb1, ub }, Interval::Unbounded { lb: lb2 })
            | (Interval::Unbounded { lb: lb1 }, Interval::Bounded { lb: lb2, ub }) => {
                Interval::bounded(*lb1.max(lb2), *ub)
            }
            (Interval::Unbounded { lb: lb1 }, Interval::Unbounded { lb: lb2 }) => {
                Interval::Unbounded { lb: *lb1.max(lb2) }
            }
        }
    }
}

impl<T: Integer + Unsigned + Copy> Interval<T> {
    pub fn merge<Annotation: Clone + std::cmp::Eq>(
        intervals: Vec<(Self, Annotation)>,
    ) -> Vec<(Self, Vec<Annotation>)> {
        // Create a list of events, each with a time, a boolean indicating if it's an entry or exit event, and the value
        // A value becomes active at the time of an entry event and inactive at the time of an exit event
        // For each interval, we generate an entry event at the lower endpoint and an exit event at the upper endpoint
        let mut events: Vec<_> = intervals
            .into_iter()
            .filter(|(int, _)| !int.is_empty())
            .flat_map(|(int, val)| match int {
                Interval::Bounded { lb, ub } => {
                    vec![(lb, true, val.clone()), (ub, false, val)]
                }
                Interval::Unbounded { lb } => {
                    vec![(lb, true, val)]
                }
                Interval::Empty => unreachable!(),
            })
            .collect();
        // Sort by time ascending (entry events come before exit events at the same time)
        events.sort_unstable_by_key(|(time, is_entry, _)| (*time, *is_entry));

        let mut merged = Vec::new();
        let mut active = Vec::new();
        let mut start = T::zero();
        for (time, is_entry, val) in events {
            // Entry events complete the interval until time - 1 (because it becomes active at time)
            // Exit events complete the interval until time (because it becomes inactive at time)
            // Since we process entry events first, we correctly get unitary intervals if both entries and exits happen at the same time
            // Entry events at time 0 never complete an interval
            if !is_entry || time > T::zero() {
                let end = if is_entry { time - T::one() } else { time };
                if end >= start && !active.is_empty() {
                    // Create a new interval with all active values
                    merged.push((Interval::bounded(start, end), active.clone()));
                }
                // The next interval always starts one step after the one we just completed
                start = end + T::one();
            }

            // Activate or deactivate the value
            if is_entry {
                active.push(val);
            } else {
                active.retain(|v| v != &val);
            }
        }

        // If there are active values at the end, we need to create a final interval
        if !active.is_empty() {
            merged.push((Interval::unbounded(start), active));
        }

        merged
    }
}

impl<T: Ord> Default for Interval<T> {
    fn default() -> Self {
        Interval::empty()
    }
}

impl<T: Integer + Unsigned + Copy> std::ops::Add for Interval<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (Interval::Bounded { lb: lb1, ub: ub1 }, Interval::Bounded { lb: lb2, ub: ub2 }) => {
                Interval::bounded(lb1 + lb2, ub1 + ub2)
            }
            (Interval::Bounded { lb: lb1, .. }, Interval::Unbounded { lb: lb2 })
            | (Interval::Unbounded { lb: lb1 }, Interval::Bounded { lb: lb2, .. })
            | (Interval::Unbounded { lb: lb1 }, Interval::Unbounded { lb: lb2 }) => {
                Interval::unbounded(lb1 + lb2)
            }
        }
    }
}

impl<T: Integer + Unsigned + SaturatingSub + Copy> std::ops::Sub for Interval<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (
                Interval::Bounded {
                    lb: lb_min,
                    ub: ub_min,
                },
                Interval::Bounded {
                    lb: lb_sub,
                    ub: ub_sub,
                },
            ) => {
                if ub_min >= lb_sub {
                    Interval::bounded(lb_min.saturating_sub(&ub_sub), ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { ub: ub_min, .. }, Interval::Unbounded { lb: lb_sub }) => {
                if ub_min >= lb_sub {
                    Interval::bounded(T::zero(), ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { ub: ub_sub, .. }) => {
                Interval::unbounded(lb_min.saturating_sub(&ub_sub))
            }
            (Interval::Unbounded { .. }, Interval::Unbounded { .. }) => {
                Interval::unbounded(T::zero())
            }
        }
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> Interval<T> {
    pub fn minkowski_difference(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) => Interval::empty(),
            (_, Interval::Empty) => Interval::unbounded(T::zero()),
            (
                Interval::Bounded {
                    lb: lb_min,
                    ub: ub_min,
                },
                Interval::Bounded {
                    lb: lb_sub,
                    ub: ub_sub,
                },
            ) => {
                if ub_min >= ub_sub {
                    Interval::bounded(lb_min.saturating_sub(&lb_sub), ub_min - ub_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { .. }, Interval::Unbounded { .. }) => Interval::empty(),
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { lb: lb_sub, .. })
            | (Interval::Unbounded { lb: lb_min }, Interval::Unbounded { lb: lb_sub }) => {
                Interval::unbounded(lb_min.saturating_sub(&lb_sub))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_merge() {
        let intervals = vec![
            (Interval::bounded(1_u32, 3), 1),
            (Interval::bounded(2, 4), 2),
            (Interval::bounded(5, 8), 3),
            (Interval::unbounded(7), 4),
        ];

        let merged = Interval::merge(intervals);

        assert_eq!(
            merged.into_iter().collect::<HashSet<_>>(),
            vec![
                (Interval::singleton(1), vec![1]),
                (Interval::bounded(2, 3), vec![1, 2]),
                (Interval::singleton(4), vec![2]),
                (Interval::bounded(5, 6), vec![3]),
                (Interval::bounded(7, 8), vec![3, 4]),
                (Interval::unbounded(9), vec![4]),
            ]
            .into_iter()
            .collect::<HashSet<_>>()
        );
    }
}
