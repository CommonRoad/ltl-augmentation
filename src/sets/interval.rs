use num::{traits::SaturatingSub, Integer, Unsigned};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

    pub fn singular(v: T) -> Self
    where
        T: Copy,
    {
        Interval::Bounded { lb: v, ub: v }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }
}

impl<T: Integer + Unsigned + Copy> Interval<T> {
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
