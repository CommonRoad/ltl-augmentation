use crate::clean::sets::interval::Interval;

pub mod boolean;
pub mod kleene;
pub mod monitor;

pub trait Logical {
    fn negation(&self) -> Self;
    fn conjunction(&self, other: &Self) -> Self;
    fn until(&self, until_interval: &Interval, other: &Self) -> Self;

    fn disjunction(&self, other: &Self) -> Self
    where
        Self: std::marker::Sized,
    {
        self.negation().conjunction(&other.negation()).negation()
    }

    fn release(&self, release_interval: &Interval, other: &Self) -> Self
    where
        Self: std::marker::Sized,
    {
        self.negation()
            .until(release_interval, &other.negation())
            .negation()
    }
}
