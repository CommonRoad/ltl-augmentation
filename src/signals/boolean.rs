use num::{Integer, Unsigned};

use crate::{sets::interval::Interval, signals::signal::Signal};

impl<T: Integer + Unsigned + Copy> Signal<T, bool> {
    pub fn from_positive_intervals(positive_intervals: &[Interval<T>]) -> Self {
        let mut signal = Signal::uniform(false);
        for interval in positive_intervals {
            signal.set(interval, true);
        }
        signal
    }

    pub fn from_negative_intervals(negative_intervals: &[Interval<T>]) -> Self {
        let mut signal = Signal::uniform(true);
        for interval in negative_intervals {
            signal.set(interval, false);
        }
        signal
    }
}
