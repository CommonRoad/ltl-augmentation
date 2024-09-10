use std::{collections::HashSet, rc::Rc};

use crate::clean::{
    knowledge_graph::KnowledgeGraph, sequence::PlainSequence, trace::Trace, truth_values::Kleene,
};

use super::NormalizedSequence;

pub type KnowledgeSequence = PlainSequence<KnowledgeGraph>;

impl KnowledgeSequence {
    pub fn kleene_trace(&self, aps: &HashSet<Rc<str>>) -> Trace<Kleene> {
        Trace::from(
            aps.iter()
                .map(|ap| {
                    (
                        ap.clone(),
                        NormalizedSequence::from(self.map(|kg| kg.get_kleene_evaluation(ap))),
                    )
                })
                .collect(),
        )
    }
}
