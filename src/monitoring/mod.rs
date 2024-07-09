use itertools::iproduct;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{sets::interval::Interval, signal::Signal};

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

impl<T: Integer + Unsigned + SaturatingSub + Copy> Logical<T> for Signal<T, bool> {
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
            .filter_map(|(lhs_interval, rhs_interval)| {
                match until_semantics(&lhs_interval, until_interval, &rhs_interval) {
                    Interval::Empty => None,
                    interval => Some(interval),
                }
            })
            .collect();
        let signal = Signal::uniform(false);
        // TODO: Add positive intervals
        signal
    }

    fn release(&self, release_interval: &Interval<T>, other: &Self) -> Self {
        let lhs_intervals = self.intervals_where_eq(&false);
        let rhs_intervals = other.intervals_where_eq(&false);
        let negative_intervals: Vec<_> = iproduct!(lhs_intervals, rhs_intervals)
            .filter_map(|(lhs_interval, rhs_interval)| {
                match until_semantics(&lhs_interval, release_interval, &rhs_interval) {
                    Interval::Empty => None,
                    interval => Some(interval),
                }
            })
            .collect();
        let signal = Signal::uniform(true);
        // TODO: Add negative intervals
        signal
    }
}

fn until_semantics<T: Integer + Unsigned + SaturatingSub + Copy>(
    lhs_interval: &Interval<T>,
    until_interval: &Interval<T>,
    rhs_interval: &Interval<T>,
) -> Interval<T> {
    // TODO: Check if we need to make the lhs interval 1 larger (to meet correct semantics of until)
    // also we might need to change this to account for the different semantics in MLTL (lhs does not need to hold before a)
    let intersection = lhs_interval.intersect(rhs_interval);
    let shift = intersection - *until_interval;
    shift.intersect(lhs_interval)
}
