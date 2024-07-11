use std::borrow::Borrow;

use num::{Integer, Unsigned};

use crate::{sets::interval::Interval, signals::signal::Signal};

pub type BooleanSignal<T> = Signal<T, bool>;

impl<T: Integer + Unsigned + Copy> BooleanSignal<T> {
    pub fn from_positive_intervals<B>(positive_intervals: impl IntoIterator<Item = B>) -> Self
    where
        B: Borrow<Interval<T>>,
    {
        let mut signal = Signal::uniform(false);
        for interval in positive_intervals {
            signal.set(interval.borrow(), true);
        }
        signal
    }

    pub fn from_negative_intervals<B>(negative_intervals: impl IntoIterator<Item = B>) -> Self
    where
        B: Borrow<Interval<T>>,
    {
        let mut signal = Signal::uniform(true);
        for interval in negative_intervals {
            signal.set(interval.borrow(), false);
        }
        signal
    }
}
