use crate::sets::interval::Interval;

pub mod boolean;
pub mod kleene;

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
