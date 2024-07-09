use itertools::iproduct;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{sets::interval::Interval, signals::signal::Signal};

pub trait Logical<T> {
    fn negation(&self) -> Self;
    fn conjunction(&self, other: &Self) -> Self;
    fn until(&self, until_interval: &Interval<T>, other: &Self) -> Self;

    fn disjunction(&self, other: &Self) -> Self
    where
        Self: std::marker::Sized,
    {
        self.negation().conjunction(&other.negation()).negation()
    }

    fn release(&self, release_interval: &Interval<T>, other: &Self) -> Self
    where
        Self: std::marker::Sized,
    {
        self.negation()
            .until(release_interval, &other.negation())
            .negation()
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub + std::fmt::Debug> Logical<T>
    for Signal<T, bool>
{
    fn negation(&self) -> Self {
        self.map(|v| !v)
    }

    fn conjunction(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a & b)
    }

    fn disjunction(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a | b)
    }

    fn until(&self, until_interval: &Interval<T>, other: &Self) -> Self {
        let lhs_intervals = self.intervals_where_eq(&true);
        let rhs_intervals = other.intervals_where_eq(&true);
        let positive_intervals: Vec<_> = iproduct!(lhs_intervals, rhs_intervals)
            .flat_map(|(lhs_interval, rhs_interval)| {
                positive_until_semantics(&lhs_interval, until_interval, &rhs_interval)
            })
            .collect();
        Signal::from_positive_intervals(&positive_intervals)
    }

    fn release(&self, release_interval: &Interval<T>, other: &Self) -> Self {
        let lhs_intervals = self.intervals_where_eq(&false);
        let rhs_intervals = other.intervals_where_eq(&false);
        let negative_intervals: Vec<_> = iproduct!(lhs_intervals, rhs_intervals)
            .flat_map(|(lhs_interval, rhs_interval)| {
                positive_until_semantics(&lhs_interval, release_interval, &rhs_interval)
            })
            .collect();
        Signal::from_negative_intervals(&negative_intervals)
    }
}

fn positive_until_semantics<T: Integer + Unsigned + SaturatingSub + Copy>(
    lhs_interval: &Interval<T>,
    until_interval: &Interval<T>,
    rhs_interval: &Interval<T>,
) -> impl Iterator<Item = Interval<T>> {
    let lhs_enlarged = match lhs_interval {
        Interval::Bounded { lb, ub } => Interval::bounded(*lb, *ub + T::one()),
        _ => *lhs_interval,
    };
    let to_lb = match until_interval {
        Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => Interval::singular(*lb),
        _ => *until_interval,
    };
    let lb_to_ub = match until_interval {
        Interval::Bounded { lb, ub } => Interval::bounded(T::zero(), *ub - *lb),
        Interval::Unbounded { .. } => Interval::unbounded(T::zero()),
        _ => *until_interval,
    };

    let i1 = (lhs_enlarged.intersect(rhs_interval) - lb_to_ub).intersect(lhs_interval) - to_lb;
    let i2 = *rhs_interval - to_lb;

    [i1, i2].into_iter().filter(|i| !i.is_empty())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_until_1() {
        let lhs = Signal::from_positive_intervals(&[Interval::bounded(2_u32, 4)]);

        let rhs =
            Signal::from_positive_intervals(&[Interval::bounded(5, 7), Interval::bounded(10, 12)]);

        let until = lhs.until(&Interval::bounded(2, 5), &rhs);

        assert_eq!(
            until,
            Signal::from_positive_intervals(&[Interval::bounded(0, 5), Interval::bounded(8, 10)])
        );
    }

    #[test]
    fn test_until_2() {
        let lhs =
            Signal::from_positive_intervals(&[Interval::singular(0_u32), Interval::unbounded(3)]);

        let rhs =
            Signal::from_positive_intervals(&[Interval::bounded(0, 3), Interval::unbounded(6)]);

        let until = lhs.until(&Interval::bounded(0, 1), &rhs);

        assert_eq!(
            until,
            Signal::from_positive_intervals(&[Interval::bounded(0, 3), Interval::unbounded(5)])
        );
    }

    #[test]
    fn test_until_3() {
        let lhs = Signal::from_positive_intervals(&[Interval::unbounded(2_u32)]);

        let rhs = Signal::from_positive_intervals(&[Interval::bounded(0, 1)]);

        let until = lhs.until(&Interval::bounded(0, 1), &rhs);

        assert_eq!(
            until,
            Signal::from_positive_intervals(&[Interval::bounded(0, 1)])
        );
    }

    #[test]
    fn test_until_4() {
        let lhs = Signal::from_positive_intervals(&[Interval::singular(1_u32)]);

        let rhs = Signal::from_positive_intervals(&[Interval::unbounded(2)]);

        let until = lhs.until(&Interval::bounded(0, 3), &rhs);

        assert_eq!(
            until,
            Signal::from_positive_intervals(&[Interval::unbounded(1)])
        );
    }

    #[test]
    fn test_until_5() {
        let lhs = Signal::from_positive_intervals(&[Interval::unbounded(2_u32)]);

        let rhs =
            Signal::from_positive_intervals(&[Interval::bounded(0, 1), Interval::unbounded(5)]);

        let until = lhs.until(&Interval::bounded(1, 3), &rhs);

        assert_eq!(
            until,
            Signal::from_positive_intervals(&[Interval::singular(0), Interval::unbounded(2)])
        );
    }
}
