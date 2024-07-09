use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{sets::interval::Interval, signals::kleene::KleeneSignal};

use super::Logical;

impl<T: Integer + Unsigned + Copy + SaturatingSub> Logical<T> for KleeneSignal<T> {
    fn negation(&self) -> Self {
        KleeneSignal::from_approximations(self.under().negation(), self.over().negation())
    }

    fn conjunction(&self, other: &Self) -> Self {
        KleeneSignal::from_approximations(
            self.over().conjunction(other.over()),
            self.under().conjunction(other.under()),
        )
    }

    fn disjunction(&self, other: &Self) -> Self {
        KleeneSignal::from_approximations(
            self.over().disjunction(other.over()),
            self.under().disjunction(other.under()),
        )
    }

    fn until(&self, until_interval: &Interval<T>, other: &Self) -> Self {
        KleeneSignal::from_approximations(
            self.over().until(until_interval, other.over()),
            self.under().until(until_interval, other.under()),
        )
    }

    fn release(&self, release_interval: &Interval<T>, other: &Self) -> Self {
        KleeneSignal::from_approximations(
            self.over().release(release_interval, other.over()),
            self.under().release(release_interval, other.under()),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::signals::{kleene::Kleene, signal::Signal};

    use super::*;

    #[test]
    fn test_disjunction() {
        let lhs = KleeneSignal::from(Signal::indicator(
            Interval::bounded(2_u32, 4),
            Kleene::True,
            Kleene::Unknown,
        ));
        let rhs = KleeneSignal::from(Signal::indicator(
            Interval::bounded(5, 7),
            Kleene::True,
            Kleene::False,
        ));
        let expected = KleeneSignal::from(Signal::indicator(
            Interval::bounded(2_u32, 7),
            Kleene::True,
            Kleene::Unknown,
        ));

        let actual = lhs.disjunction(&rhs);

        assert_eq!(actual, expected);
    }
}
