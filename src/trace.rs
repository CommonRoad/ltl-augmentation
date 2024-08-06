use std::collections::HashMap;

use crate::signals::signal::Signal;

pub struct Trace<'a, T, V>(HashMap<&'a str, Signal<T, V>>);

impl<'a, T, V> Trace<'a, T, V> {
    pub fn from(signals: HashMap<&'a str, Signal<T, V>>) -> Self {
        Trace(signals)
    }

    pub fn get_ap_signal(&self, name: &str) -> Option<&Signal<T, V>> {
        self.0.get(name)
    }
}
