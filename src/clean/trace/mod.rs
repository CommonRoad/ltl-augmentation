use std::collections::HashMap;

use super::{formula::atomic_proposition::AtomicProposition, sequence::NormalizedSequence};

pub mod parser;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace<V>(HashMap<AtomicProposition, NormalizedSequence<V>>);

impl<V> Trace<V> {
    pub fn from(sequences: HashMap<AtomicProposition, NormalizedSequence<V>>) -> Self {
        Trace(sequences)
    }

    pub fn get_sequences(&self) -> &HashMap<AtomicProposition, NormalizedSequence<V>> {
        &self.0
    }

    pub fn get_ap_sequence(&self, ap: &AtomicProposition) -> Option<&NormalizedSequence<V>> {
        self.0.get(ap)
    }
}
