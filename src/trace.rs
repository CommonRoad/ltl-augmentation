use std::{collections::HashMap, rc::Rc};

use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{sets::interval_set::IntervalSet, signals::signal::Signal};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace<T, V>(HashMap<Rc<str>, Signal<T, V>>);

impl<T: Integer + Unsigned + Copy + SaturatingSub, V> Trace<T, V> {
    pub fn from(signals: HashMap<Rc<str>, Signal<T, V>>) -> Self {
        Trace(signals)
    }

    pub fn get_ap_signal(&self, name: &str) -> Option<&Signal<T, V>> {
        self.0.get(name)
    }

    pub fn set_ap(&mut self, name: Rc<str>, intervals: &IntervalSet<T>, value: V)
    where
        V: Eq + Default + Clone,
    {
        let signal = self.0.entry(name).or_insert_with(|| Signal::new());
        intervals.get_intervals().iter().for_each(|interval| {
            signal.set(interval, value.clone());
        });
    }
}
