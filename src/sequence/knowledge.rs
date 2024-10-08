use std::collections::HashSet;

use super::{NormalizedSequence, Sequence};
use crate::formula::literal::Literal;
use crate::{
    knowledge_graph::{KnowledgeGraph, KnowledgeGraphEdge},
    sequence::PlainSequence,
    trace::Trace,
    truth_values::Kleene,
};

pub type KnowledgeSequence = PlainSequence<KnowledgeGraph>;

impl KnowledgeSequence {
    pub fn kleene_trace(&self) -> Trace<Kleene> {
        let aps: HashSet<_> = self
            .values
            .iter()
            .flat_map(|(_, kg)| kg.collect_aps())
            .collect();
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

impl From<Trace<Kleene>> for KnowledgeSequence {
    fn from(value: Trace<Kleene>) -> Self {
        let mut edges = PlainSequence::uniform(Vec::new());
        for (ap, kleene_seq) in value.get_sequences() {
            edges = edges.combine(&kleene_seq.0, |edges, kleene_val| match kleene_val {
                Kleene::True => edges
                    .iter()
                    .cloned()
                    .chain(std::iter::once(KnowledgeGraphEdge::IsTrue(
                        Literal::Positive(ap.clone()),
                    )))
                    .collect(),
                Kleene::False => edges
                    .iter()
                    .cloned()
                    .chain(std::iter::once(KnowledgeGraphEdge::IsFalse(
                        Literal::Positive(ap.clone()),
                    )))
                    .collect(),
                Kleene::Unknown => edges.clone(),
            });
        }
        let edges_normalized = NormalizedSequence::from(edges);
        KnowledgeSequence::from(edges_normalized)
    }
}

impl<I: IntoIterator<Item = KnowledgeGraphEdge>> From<NormalizedSequence<I>> for KnowledgeSequence {
    fn from(value: NormalizedSequence<I>) -> Self {
        value.0.into_map(|edges| KnowledgeGraph::from_iter(edges))
    }
}
