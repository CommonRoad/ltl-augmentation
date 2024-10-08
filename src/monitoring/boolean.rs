use itertools::iproduct;

use crate::{
    sequence::{boolean::BooleanSequence, NormalizedSequence, Sequence},
    sets::interval::Interval,
};

use super::Logical;

pub type BooleanMonitorSequence = NormalizedSequence<bool>;

impl Logical for BooleanMonitorSequence {
    fn negation(&self) -> Self {
        self.map(|v| !v)
    }

    fn conjunction(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a & b)
    }

    fn disjunction(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a | b)
    }

    fn until(&self, until_interval: &Interval, other: &Self) -> Self {
        let lhs_intervals = self.intervals_where_eq(&true);
        let rhs_intervals = other.intervals_where_eq(&true);
        let positive_intervals: Vec<_> = iproduct!(lhs_intervals, rhs_intervals)
            .flat_map(|(lhs_interval, rhs_interval)| {
                positive_until_semantics(&lhs_interval, until_interval, &rhs_interval)
            })
            .collect();
        BooleanSequence::from_positive_intervals(positive_intervals)
    }

    fn globally(&self, globally_interval: &Interval) -> Self {
        let sub_intervals = self.intervals_where_eq(&false);
        let negative_intervals: Vec<_> = sub_intervals
            .into_iter()
            .map(|sub_interval| negative_globally_semantics(&sub_interval, globally_interval))
            .collect();
        BooleanSequence::from_negative_intervals(negative_intervals)
    }
}

fn positive_until_semantics(
    lhs_interval: &Interval,
    until_interval: &Interval,
    rhs_interval: &Interval,
) -> impl Iterator<Item = Interval> {
    let lhs_enlarged = match lhs_interval {
        Interval::Bounded { lb, ub } => Interval::bounded(*lb, *ub + 1),
        _ => *lhs_interval,
    };
    let to_lb = match until_interval {
        Interval::Bounded { lb, .. } | Interval::Unbounded { lb } => Interval::singleton(*lb),
        _ => *until_interval,
    };
    let lb_to_ub = match until_interval {
        Interval::Bounded { lb, ub } => Interval::bounded(0, *ub - *lb),
        Interval::Unbounded { .. } => Interval::unbounded(0),
        _ => *until_interval,
    };

    let i1 = (lhs_enlarged.intersect(rhs_interval) - lb_to_ub).intersect(lhs_interval) - to_lb;
    let i2 = *rhs_interval - to_lb;

    [i1, i2].into_iter().filter(|i| !i.is_empty())
}

fn negative_globally_semantics(sub_interval: &Interval, globally_interval: &Interval) -> Interval {
    *sub_interval - *globally_interval
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_until_1() {
        let lhs = BooleanSequence::from_positive_intervals([Interval::bounded(2_u32, 4)]);

        let rhs = BooleanSequence::from_positive_intervals([
            Interval::bounded(5, 7),
            Interval::bounded(10, 12),
        ]);

        let until = lhs.until(&Interval::bounded(2, 5), &rhs);

        assert_eq!(
            until,
            BooleanSequence::from_positive_intervals([
                Interval::bounded(0, 5),
                Interval::bounded(8, 10)
            ])
        );
    }

    #[test]
    fn test_until_2() {
        let lhs = BooleanSequence::from_positive_intervals([
            Interval::singleton(0_u32),
            Interval::unbounded(3),
        ]);

        let rhs = BooleanSequence::from_positive_intervals([
            Interval::bounded(0, 3),
            Interval::unbounded(6),
        ]);

        let until = lhs.until(&Interval::bounded(0, 1), &rhs);

        assert_eq!(
            until,
            BooleanSequence::from_positive_intervals([
                Interval::bounded(0, 3),
                Interval::unbounded(5)
            ])
        );
    }

    #[test]
    fn test_until_3() {
        let lhs = BooleanSequence::from_positive_intervals([Interval::unbounded(2_u32)]);

        let rhs = BooleanSequence::from_positive_intervals([Interval::bounded(0, 1)]);

        let until = lhs.until(&Interval::bounded(0, 1), &rhs);

        assert_eq!(
            until,
            BooleanSequence::from_positive_intervals([Interval::bounded(0, 1)])
        );
    }

    #[test]
    fn test_until_4() {
        let lhs = BooleanSequence::from_positive_intervals([Interval::singleton(1_u32)]);

        let rhs = BooleanSequence::from_positive_intervals([Interval::unbounded(2)]);

        let until = lhs.until(&Interval::bounded(0, 3), &rhs);

        assert_eq!(
            until,
            BooleanSequence::from_positive_intervals([Interval::unbounded(1)])
        );
    }

    #[test]
    fn test_until_5() {
        let lhs = BooleanSequence::from_positive_intervals([Interval::unbounded(2_u32)]);

        let rhs = BooleanSequence::from_positive_intervals([
            Interval::bounded(0, 1),
            Interval::unbounded(5),
        ]);

        let until = lhs.until(&Interval::bounded(1, 3), &rhs);

        assert_eq!(
            until,
            BooleanSequence::from_positive_intervals([
                Interval::singleton(0),
                Interval::unbounded(2)
            ])
        );
    }
}
