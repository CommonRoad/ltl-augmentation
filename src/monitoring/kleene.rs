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
