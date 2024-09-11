use std::{collections::HashSet, rc::Rc};

use crate::clean::{
    formula::AtomicProposition,
    knowledge_graph::{KnowledgeGraph, KnowledgeGraphEdge, Literal},
    sequence::PlainSequence,
    trace::Trace,
    truth_values::Kleene,
};

use super::{NormalizedSequence, Sequence};

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

impl From<Trace<Kleene>> for KnowledgeSequence {
    fn from(value: Trace<Kleene>) -> Self {
        let mut edges = PlainSequence::uniform(Vec::new());
        for (ap, kleene_seq) in value.get_sequences() {
            edges = edges.combine(&kleene_seq.0, |edges, kleene_val| match kleene_val {
                Kleene::True => edges
                    .iter()
                    .cloned()
                    .chain(std::iter::once(KnowledgeGraphEdge::IsTrue(Literal::Atom(
                        AtomicProposition {
                            name: ap.clone(),
                            negated: false,
                        },
                    ))))
                    .collect(),
                Kleene::False => edges
                    .iter()
                    .cloned()
                    .chain(std::iter::once(KnowledgeGraphEdge::IsFalse(Literal::Atom(
                        AtomicProposition {
                            name: ap.clone(),
                            negated: false,
                        },
                    ))))
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
