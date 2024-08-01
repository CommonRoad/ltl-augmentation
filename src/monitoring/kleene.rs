use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    sets::interval::Interval,
    signals::{signal::Signal, truth_values::Kleene},
};

use super::{boolean::BooleanMonitorSignal, Logical};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KleeneMonitorSignal<T> {
    over: BooleanMonitorSignal<T>,
    under: BooleanMonitorSignal<T>,
}

impl<T: Integer + Unsigned + Copy> KleeneMonitorSignal<T> {
    pub fn new() -> Self {
        KleeneMonitorSignal::uniform(Kleene::default())
    }

    pub fn from_approximations(
        over: BooleanMonitorSignal<T>,
        under: BooleanMonitorSignal<T>,
    ) -> Self {
        KleeneMonitorSignal { over, under }
    }

    pub fn uniform(k: Kleene) -> Self {
        KleeneMonitorSignal {
            over: Signal::uniform(k != Kleene::False),
            under: Signal::uniform(k != Kleene::True),
        }
    }

    pub fn over(&self) -> &BooleanMonitorSignal<T> {
        &self.over
    }

    pub fn under(&self) -> &BooleanMonitorSignal<T> {
        &self.under
    }
}

impl<T: Integer + Unsigned + Copy> Default for KleeneMonitorSignal<T> {
    fn default() -> Self {
        KleeneMonitorSignal::new()
    }
}

impl<T: Integer + Unsigned + Copy> From<Signal<T, Kleene>> for KleeneMonitorSignal<T> {
    fn from(signal: Signal<T, Kleene>) -> Self {
        let over = signal.map(|&k| k != Kleene::False);
        let under = signal.map(|&k| k == Kleene::True);
        KleeneMonitorSignal { over, under }
    }
}

impl<T: Integer + Unsigned + Copy> From<KleeneMonitorSignal<T>> for Signal<T, Kleene> {
    fn from(signal: KleeneMonitorSignal<T>) -> Self {
        signal.over.combine(&signal.under, |&o, &u| match (o, u) {
            (true, true) => Kleene::True,
            (false, false) => Kleene::False,
            (true, false) => Kleene::Unknown,
            (false, true) => {
                unreachable!("Overapproximation is always more true than underapproximation")
            }
        })
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> Logical<T> for KleeneMonitorSignal<T> {
    fn negation(&self) -> Self {
        KleeneMonitorSignal::from_approximations(self.under().negation(), self.over().negation())
    }

    fn conjunction(&self, other: &Self) -> Self {
        KleeneMonitorSignal::from_approximations(
            self.over().conjunction(other.over()),
            self.under().conjunction(other.under()),
        )
    }

    fn disjunction(&self, other: &Self) -> Self {
        KleeneMonitorSignal::from_approximations(
            self.over().disjunction(other.over()),
            self.under().disjunction(other.under()),
        )
    }

    fn until(&self, until_interval: &Interval<T>, other: &Self) -> Self {
        KleeneMonitorSignal::from_approximations(
            self.over().until(until_interval, other.over()),
            self.under().until(until_interval, other.under()),
        )
    }

    fn release(&self, release_interval: &Interval<T>, other: &Self) -> Self {
        KleeneMonitorSignal::from_approximations(
            self.over().release(release_interval, other.over()),
            self.under().release(release_interval, other.under()),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::signals::{signal::Signal, truth_values::Kleene};

    use super::*;

    #[test]
    fn test_disjunction() {
        let lhs = KleeneMonitorSignal::from(Signal::indicator(
            &Interval::bounded(2_u32, 4),
            Kleene::True,
            Kleene::Unknown,
        ));
        let rhs = KleeneMonitorSignal::from(Signal::indicator(
            &Interval::bounded(5, 7),
            Kleene::True,
            Kleene::False,
        ));
        let expected = KleeneMonitorSignal::from(Signal::indicator(
            &Interval::bounded(2_u32, 7),
            Kleene::True,
            Kleene::Unknown,
        ));

        let actual = lhs.disjunction(&rhs);

        assert_eq!(actual, expected);
    }
}
