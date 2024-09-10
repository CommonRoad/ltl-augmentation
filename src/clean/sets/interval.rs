use std::fmt::Display;

use crate::clean::sequence::Time;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Interval {
    Empty,
    Bounded { lb: Time, ub: Time },
    Unbounded { lb: Time },
}

impl Interval {
    pub fn empty() -> Self {
        Interval::Empty
    }

    pub fn bounded(lb: Time, ub: Time) -> Self {
        if lb > ub {
            Interval::Empty
        } else {
            Interval::Bounded { lb, ub }
        }
    }

    pub fn bounded_ub_excl(lb: Time, ub: Time) -> Self {
        if lb >= ub {
            Interval::Empty
        } else {
            Interval::Bounded { lb, ub: ub - 1 }
        }
    }

    pub fn unbounded(lb: Time) -> Self {
        Interval::Unbounded { lb }
    }

    pub fn singleton(v: Time) -> Self
    where
        Time: Copy,
    {
        Interval::Bounded { lb: v, ub: v }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }

    pub fn is_singleton(&self) -> bool {
        matches!(self, Interval::Bounded { lb, ub } if lb == ub)
    }

    pub fn contains(&self, v: &Time) -> bool {
        match self {
            Interval::Empty => false,
            Interval::Bounded { lb, ub } => lb <= v && v <= ub,
            Interval::Unbounded { lb } => lb <= v,
        }
    }

    pub fn lb(&self) -> Option<&Time> {
        match self {
            Interval::Empty => None,
            Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => Some(lb),
        }
    }

    pub fn ub(&self) -> Option<&Time> {
        match self {
            Interval::Empty | Interval::Unbounded { .. } => None,
            Interval::Bounded { ub, .. } => Some(ub),
        }
    }

    pub fn intersect(&self, other: &Self) -> Self {
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

impl Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Interval::Empty => write!(f, "∅"),
            Interval::Bounded { lb, ub } => write!(f, "[{}, {}]", lb, ub),
            Interval::Unbounded { lb } => write!(f, "[{}, ∞)", lb),
        }
    }
}

impl Default for Interval {
    fn default() -> Self {
        Interval::empty()
    }
}

impl Interval {
    pub fn minkowski_sum(self, rhs: Self) -> Self {
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

    pub fn minkowski_difference(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) => Interval::empty(),
            (_, Interval::Empty) => Interval::unbounded(0),
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
                    Interval::bounded(lb_min.saturating_sub(lb_sub), ub_min - ub_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { .. }, Interval::Unbounded { .. }) => Interval::empty(),
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { lb: lb_sub, .. })
            | (Interval::Unbounded { lb: lb_min }, Interval::Unbounded { lb: lb_sub }) => {
                Interval::unbounded(lb_min.saturating_sub(lb_sub))
            }
        }
    }

    pub fn back_shift(self, rhs: Self) -> Self {
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
                    Interval::bounded(lb_min.saturating_sub(ub_sub), ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { ub: ub_min, .. }, Interval::Unbounded { lb: lb_sub }) => {
                if ub_min >= lb_sub {
                    Interval::bounded(0, ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { ub: ub_sub, .. }) => {
                Interval::unbounded(lb_min.saturating_sub(ub_sub))
            }
            (Interval::Unbounded { .. }, Interval::Unbounded { .. }) => Interval::unbounded(0),
        }
    }

    // Determine Minkowski sum of self with every point of rhs and return the intersection of the results
    pub fn minkowski_sum_intersection(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) => Interval::empty(),
            (_, Interval::Empty) => Interval::unbounded(0),
            (
                Interval::Bounded {
                    lb: lb_lhs,
                    ub: ub_lhs,
                },
                Interval::Bounded {
                    lb: lb_rhs,
                    ub: ub_rhs,
                },
            ) => Interval::bounded(lb_lhs + ub_rhs, ub_lhs + lb_rhs),
            (Interval::Bounded { .. }, Interval::Unbounded { .. })
            | (Interval::Unbounded { .. }, Interval::Unbounded { .. }) => Interval::empty(),
            (Interval::Unbounded { lb: lb_lhs }, Interval::Bounded { ub: ub_rhs, .. }) => {
                Interval::unbounded(lb_lhs + ub_rhs)
            }
        }
    }
}

impl std::ops::Add for Interval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.minkowski_sum(rhs)
    }
}

impl std::ops::Sub for Interval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.back_shift(rhs)
    }
}

pub struct IntervalIterator {
    next: Option<Time>,
    ub: Option<Time>,
}

impl Iterator for IntervalIterator {
    type Item = Time;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.next;
        if let Some(x) = self.next.as_mut() {
            *x += 1;
        }
        if self.ub.is_some_and(|ub| self.next.is_some_and(|x| x > ub)) {
            self.next = None;
        }
        ret
    }
}

impl IntoIterator for Interval {
    type Item = Time;

    type IntoIter = IntervalIterator;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Interval::Bounded { lb, ub } => IntervalIterator {
                next: Some(lb),
                ub: Some(ub),
            },
            Interval::Unbounded { lb } => IntervalIterator {
                next: Some(lb),
                ub: None,
            },
            Interval::Empty => IntervalIterator {
                next: None,
                ub: None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;

    #[test]
    fn test_iter() {
        let interval = Interval::bounded(3, 7);
        assert_eq!(interval.into_iter().collect_vec(), (3..=7).collect_vec());

        let interval = Interval::unbounded(5);
        assert_eq!(
            interval.into_iter().take(1000).collect_vec(),
            (5..).take(1000).collect_vec()
        );

        let interval = Interval::empty();
        assert_eq!(interval.into_iter().collect_vec(), vec![])
    }
}
