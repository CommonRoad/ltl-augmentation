use std::collections::HashMap;

use pyo3::prelude::*;

use crate::{
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

fn parse_proposition(proposition: &str) -> Literal {
    // match the following structure "name(parameter)"
    let mut split = proposition.split('(');
    let name = split.next().unwrap();
    if let Some(parameter) = split.next() {
        let parameter = parameter.trim_end_matches(')');
        Literal::Positive(AtomicProposition::with_parameter(name, parameter))
    } else {
        Literal::Positive(AtomicProposition::new(name))
    }
}

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
                        KnowledgeGraphEdge::IsTrue(parse_proposition(&positive_proposition))
                    })
                    .chain(
                        negative_propsitions
                            .into_iter()
                            .map(|negative_proposition| {
                                KnowledgeGraphEdge::IsFalse(parse_proposition(
                                    &negative_proposition,
                                ))
                            }),
                    )
                    .chain(implications.into_iter().map(|(lhs, rhs)| {
                        KnowledgeGraphEdge::Implication(
                            parse_proposition(&lhs),
                            parse_proposition(&rhs),
                        )
                    }))
                    .chain(equivalences.into_iter().map(|(lhs, rhs)| {
                        KnowledgeGraphEdge::Equivalence(
                            parse_proposition(&lhs),
                            parse_proposition(&rhs),
                        )
                    }))
                    .collect();
                (time, kg_edges)
            })
            .collect();
        KnowledgeSequence(knowledge::KnowledgeSequence::from(edge_sequence))
    }
}
