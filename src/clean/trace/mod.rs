use std::{collections::HashMap, sync::Arc};

use super::sequence::NormalizedSequence;

pub mod parser;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace<V>(HashMap<Arc<str>, NormalizedSequence<V>>);

impl<V> Trace<V> {
    pub fn from(sequences: HashMap<Arc<str>, NormalizedSequence<V>>) -> Self {
        Trace(sequences)
    }

    pub fn get_sequences(&self) -> &HashMap<Arc<str>, NormalizedSequence<V>> {
        &self.0
    }

    pub fn get_ap_sequence(&self, name: &str) -> Option<&NormalizedSequence<V>> {
        self.0.get(name)
    }
}
