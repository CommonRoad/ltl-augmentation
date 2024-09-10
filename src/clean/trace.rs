use std::{collections::HashMap, rc::Rc};

use super::sequence::NormalizedSequence;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace<V>(HashMap<Rc<str>, NormalizedSequence<V>>);

impl<V> Trace<V> {
    pub fn from(sequences: HashMap<Rc<str>, NormalizedSequence<V>>) -> Self {
        Trace(sequences)
    }

    pub fn get_sequences(&self) -> &HashMap<Rc<str>, NormalizedSequence<V>> {
        &self.0
    }

    pub fn get_ap_sequence(&self, name: &str) -> Option<&NormalizedSequence<V>> {
        self.0.get(name)
    }
}
