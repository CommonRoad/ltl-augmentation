use std::borrow::Borrow;

use crate::sets::interval::Interval;

use super::{NormalizedSequence, Sequence};

pub type BooleanSequence = NormalizedSequence<bool>;

impl BooleanSequence {
    pub fn from_positive_intervals<B>(positive_intervals: impl IntoIterator<Item = B>) -> Self
    where
        B: Borrow<Interval>,
    {
        let mut signal = BooleanSequence::uniform(false);
        for interval in positive_intervals {
            signal.set(interval.borrow(), true);
        }
        signal
    }

    pub fn from_negative_intervals<B>(negative_intervals: impl IntoIterator<Item = B>) -> Self
    where
        B: Borrow<Interval>,
    {
        let mut signal = BooleanSequence::uniform(true);
        for interval in negative_intervals {
            signal.set(interval.borrow(), false);
        }
        signal
    }
}
