use crate::{
    sequence::{NormalizedSequence, Sequence},
    sets::interval::Interval,
    truth_values::Kleene,
};

use super::{boolean::BooleanMonitorSequence, Logical};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KleeneMonitorSequence {
    over: BooleanMonitorSequence,
    under: BooleanMonitorSequence,
}

impl KleeneMonitorSequence {
    pub fn new() -> Self {
        KleeneMonitorSequence::uniform(Kleene::default())
    }

    pub fn from_approximations(
        over: BooleanMonitorSequence,
        under: BooleanMonitorSequence,
    ) -> Self {
        KleeneMonitorSequence { over, under }
    }

    pub fn uniform(k: Kleene) -> Self {
        KleeneMonitorSequence {
            over: BooleanMonitorSequence::uniform(k != Kleene::False),
            under: BooleanMonitorSequence::uniform(k != Kleene::True),
        }
    }

    pub fn over(&self) -> &BooleanMonitorSequence {
        &self.over
    }

    pub fn under(&self) -> &BooleanMonitorSequence {
        &self.under
    }
}

impl Default for KleeneMonitorSequence {
    fn default() -> Self {
        KleeneMonitorSequence::new()
    }
}

impl From<NormalizedSequence<Kleene>> for KleeneMonitorSequence {
    fn from(sequence: NormalizedSequence<Kleene>) -> Self {
        let over = sequence.map(|&k| k != Kleene::False);
        let under = sequence.map(|&k| k == Kleene::True);
        KleeneMonitorSequence { over, under }
    }
}

impl From<KleeneMonitorSequence> for NormalizedSequence<Kleene> {
    fn from(sequence: KleeneMonitorSequence) -> Self {
        sequence
            .over
            .combine(&sequence.under, |&o, &u| match (o, u) {
                (true, true) => Kleene::True,
                (false, false) => Kleene::False,
                (true, false) => Kleene::Unknown,
                (false, true) => {
                    unreachable!("Overapproximation is always more true than underapproximation")
                }
            })
    }
}

impl Logical for KleeneMonitorSequence {
    fn negation(&self) -> Self {
        KleeneMonitorSequence::from_approximations(self.under().negation(), self.over().negation())
    }

    fn conjunction(&self, other: &Self) -> Self {
        KleeneMonitorSequence::from_approximations(
            self.over().conjunction(other.over()),
            self.under().conjunction(other.under()),
        )
    }

    fn disjunction(&self, other: &Self) -> Self {
        KleeneMonitorSequence::from_approximations(
            self.over().disjunction(other.over()),
            self.under().disjunction(other.under()),
        )
    }

    fn until(&self, until_interval: &Interval, other: &Self) -> Self {
        KleeneMonitorSequence::from_approximations(
            self.over().until(until_interval, other.over()),
            self.under().until(until_interval, other.under()),
        )
    }

    fn globally(&self, globally_interval: &Interval) -> Self {
        KleeneMonitorSequence::from_approximations(
            self.over().globally(globally_interval),
            self.under().globally(globally_interval),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disjunction() {
        let lhs = KleeneMonitorSequence::from(NormalizedSequence::indicator(
            &Interval::bounded(2_u32, 4),
            Kleene::True,
            Kleene::Unknown,
        ));
        let rhs = KleeneMonitorSequence::from(NormalizedSequence::indicator(
            &Interval::bounded(5, 7),
            Kleene::True,
            Kleene::False,
        ));
        let expected = KleeneMonitorSequence::from(NormalizedSequence::indicator(
            &Interval::bounded(2_u32, 7),
            Kleene::True,
            Kleene::Unknown,
        ));

        let actual = lhs.disjunction(&rhs);

        assert_eq!(actual, expected);
    }
}
