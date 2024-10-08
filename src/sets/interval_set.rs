use std::borrow::Borrow;

use crate::{
    sequence::{boolean::BooleanSequence, NormalizedSequence, Sequence, Time},
    sets::interval::Interval,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntervalSet {
    included: NormalizedSequence<bool>,
}

impl IntervalSet {
    pub fn new() -> Self {
        IntervalSet {
            included: NormalizedSequence::uniform(false),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.included == NormalizedSequence::uniform(false)
    }

    pub fn max(&self) -> Option<Time> {
        if self.is_empty() {
            return None;
        }

        let included_last_change = self.included.last_change();
        if *self.included.at(included_last_change) {
            Some(Time::MAX)
        } else {
            Some(included_last_change - 1)
        }
    }

    pub fn add(&mut self, interval: &Interval) {
        self.included.set(interval, true);
    }

    pub fn remove(&mut self, interval: &Interval) {
        self.included.set(interval, false);
    }

    pub fn contains(&self, time: Time) -> bool {
        *self.included.at(time)
    }

    pub fn union(&self, other: &Self) -> Self {
        IntervalSet {
            included: self.included.combine(&other.included, |&i1, &i2| i1 || i2),
        }
    }

    pub fn intersect(&self, other: &Self) -> Self {
        IntervalSet {
            included: self.included.combine(&other.included, |&i1, &i2| i1 && i2),
        }
    }

    pub fn minkowski_sum(&self, interval: &Interval) -> Self {
        match interval {
            Interval::Empty => IntervalSet::new(),
            _ => self
                .get_intervals()
                .iter()
                .map(|&i| i + *interval)
                .collect(),
        }
    }

    pub fn minkowski_difference(&self, interval: &Interval) -> Self {
        match interval {
            Interval::Empty => IntervalSet::from(Interval::unbounded(0)),
            _ => self
                .get_intervals()
                .iter()
                .map(|&i| i.minkowski_difference(*interval))
                .collect(),
        }
    }

    pub fn back_shift(self, interval: &Interval) -> Self {
        match interval {
            Interval::Empty => IntervalSet::new(),
            _ => self
                .get_intervals()
                .iter()
                .map(|&i| i - *interval)
                .collect(),
        }
    }

    pub fn minkowski_sum_intersection(&self, interval: &Interval) -> Self {
        match interval {
            Interval::Empty => IntervalSet::from(Interval::unbounded(0)),
            _ => self
                .get_intervals()
                .iter()
                .map(|&i| i.minkowski_sum_intersection(*interval))
                .collect(),
        }
    }

    pub fn get_intervals(&self) -> Vec<Interval> {
        self.included.intervals_where_eq(&true)
    }
}

impl Default for IntervalSet {
    fn default() -> Self {
        Self::new()
    }
}

impl<B: Borrow<Interval>> From<B> for IntervalSet {
    fn from(interval: B) -> Self {
        IntervalSet {
            included: NormalizedSequence::indicator(interval.borrow(), true, false),
        }
    }
}

impl<B: Borrow<Interval>> FromIterator<B> for IntervalSet {
    fn from_iter<I: IntoIterator<Item = B>>(iter: I) -> Self {
        IntervalSet {
            included: BooleanSequence::from_positive_intervals(iter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_set() {
        let mut is = IntervalSet::new();
        assert!(is.get_intervals().is_empty());

        let i0 = Interval::bounded(1, 1);
        is.add(&i0);
        assert_eq!(is.get_intervals(), vec![i0]);
        assert!(is.contains(1));
        assert!(!is.contains(2));

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

        let mut is1 = IntervalSet::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.union(&is2);
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

        let mut is1 = IntervalSet::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.union(&is2);
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

        let mut is1 = IntervalSet::new();
        is1.add(&i1);
        is1.add(&i3);
        is1.add(&i5);

        let mut is2 = IntervalSet::new();
        is2.add(&i2);
        is2.add(&i4);
        is2.add(&i6);

        let is = is1.intersect(&is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(9, 10), i6]);
    }

    #[test]
    fn test_interval_set_intersect_singular() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(10, 20);

        let mut is1 = IntervalSet::new();
        is1.add(&i1);

        let mut is2 = IntervalSet::new();
        is2.add(&i2);

        let is = is1.intersect(&is2);
        assert_eq!(is.get_intervals(), vec![Interval::bounded(10, 10)]);
    }

    #[test]
    fn test_interval_set_intersect_unbounded() {
        let i1 = Interval::bounded(0, 6);
        let i2 = Interval::bounded(10, 20);
        let i3 = Interval::unbounded(5);

        let mut is1 = IntervalSet::new();
        is1.add(&i1);
        is1.add(&i2);

        let mut is2 = IntervalSet::new();
        is2.add(&i3);

        let is = is1.intersect(&is2);
        assert_eq!(
            is.get_intervals(),
            vec![Interval::bounded(5, 6), Interval::bounded(10, 20)]
        );
    }

    #[test]
    fn test_interval_set_minkowski_sum() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(12, 20);

        let mut is = IntervalSet::new();
        is.add(&i1);
        is.add(&i2);

        let res = is.minkowski_sum(&Interval::bounded(2, 3));
        assert_eq!(res.get_intervals(), vec![Interval::bounded(2, 23)]);
    }

    #[test]
    fn test_interval_set_back_shift() {
        let i1 = Interval::bounded(0, 10);
        let i2 = Interval::bounded(12, 20);

        let mut is = IntervalSet::new();
        is.add(&i1);
        is.add(&i2);

        let res = is.back_shift(&Interval::bounded(2, 3));
        assert_eq!(res.get_intervals(), vec![Interval::bounded(0, 18)]);
    }
}
