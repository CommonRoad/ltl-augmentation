use std::{collections::HashMap, rc::Rc};

use crate::signals::signal::Signal;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace<T, V>(HashMap<Rc<str>, Signal<T, V>>);

impl<T, V> Trace<T, V> {
    pub fn from(signals: HashMap<Rc<str>, Signal<T, V>>) -> Self {
        Trace(signals)
    }

    pub fn get_ap_signal(&self, name: &str) -> Option<&Signal<T, V>> {
        self.0.get(name)
    }
}
