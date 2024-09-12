use std::{collections::HashMap, sync::Arc};

use pyo3::prelude::*;

use crate::clean::{
    formula::{atomic_proposition::AtomicProposition, literal::Literal},
    knowledge_graph::KnowledgeGraphEdge,
    sequence::{knowledge, NormalizedSequence, Time},
};

type EdgesAtTime = (
    Vec<String>,
    Vec<String>,
    Vec<(String, String)>,
    Vec<(String, String)>,
);

#[pyclass]
pub struct KnowledgeSequence(pub knowledge::KnowledgeSequence);

#[pymethods]
impl KnowledgeSequence {
    #[new]
    fn from(edges: HashMap<Time, EdgesAtTime>) -> Self {
        let edge_sequence: NormalizedSequence<_> = edges
            .into_iter()
            .map(|(time, edges_at_time)| {
                let (positive_propsitions, negative_propsitions, implications, equivalences) =
                    edges_at_time;
                let kg_edges: Vec<_> = positive_propsitions
                    .into_iter()
                    .map(|positive_proposition| {
                        KnowledgeGraphEdge::IsTrue(Literal::Atom(AtomicProposition {
                            name: Arc::from(positive_proposition.as_str()),
                            negated: false,
                        }))
                    })
                    .chain(
                        negative_propsitions
                            .into_iter()
                            .map(|negative_proposition| {
                                KnowledgeGraphEdge::IsFalse(Literal::Atom(AtomicProposition {
                                    name: Arc::from(negative_proposition.as_str()),
                                    negated: false,
                                }))
                            }),
                    )
                    .chain(implications.into_iter().map(|(lhs, rhs)| {
                        KnowledgeGraphEdge::Implication(
                            Literal::Atom(AtomicProposition {
                                name: Arc::from(lhs.as_str()),
                                negated: false,
                            }),
                            Literal::Atom(AtomicProposition {
                                name: Arc::from(rhs.as_str()),
                                negated: false,
                            }),
                        )
                    }))
                    .chain(equivalences.into_iter().map(|(lhs, rhs)| {
                        KnowledgeGraphEdge::Equivalence(
                            Literal::Atom(AtomicProposition {
                                name: Arc::from(lhs.as_str()),
                                negated: false,
                            }),
                            Literal::Atom(AtomicProposition {
                                name: Arc::from(rhs.as_str()),
                                negated: false,
                            }),
                        )
                    }))
                    .collect();
                (time, kg_edges)
            })
            .collect();
        KnowledgeSequence(knowledge::KnowledgeSequence::from(edge_sequence))
    }
}
