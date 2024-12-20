use ltl_augmentation::{
    augmentation::Augmenter,
    formula::{atomic_proposition::AtomicProposition, literal::Literal, parser::ltl_parser},
    knowledge_graph::KnowledgeGraphEdge,
    sequence::{knowledge::KnowledgeSequence, NormalizedSequence},
};

fn main() {
    let formula = ltl_parser::formula("(G l1 & b1 -> s1) & (G l2 & b2 -> s2)")
        .expect("Syntax should be correct")
        .into();
    println!("Original formula:\n{}", &formula);
    let l1 = Literal::Positive(AtomicProposition::new("l1"));
    let b1 = Literal::Positive(AtomicProposition::new("b1"));
    let s1 = Literal::Positive(AtomicProposition::new("s1"));
    let l2 = Literal::Positive(AtomicProposition::new("l2"));
    let b2 = Literal::Positive(AtomicProposition::new("b2"));
    let s2 = Literal::Positive(AtomicProposition::new("s2"));
    let knowledge = KnowledgeSequence::from(
        [
            (
                0,
                vec![
                    KnowledgeGraphEdge::IsTrue(l2.clone()),
                    KnowledgeGraphEdge::IsTrue(b2.clone()),
                    KnowledgeGraphEdge::IsFalse(b1.clone()),
                ],
            ),
            (
                1,
                vec![
                    KnowledgeGraphEdge::Implication(b1, b2),
                    KnowledgeGraphEdge::Implication(s1, s2),
                    KnowledgeGraphEdge::Equivalence(l1, l2),
                ],
            ),
        ]
        .into_iter()
        .collect::<NormalizedSequence<_>>(),
    );
    let augmenter = Augmenter::new(knowledge);
    let augmented = augmenter.augment(&formula);
    println!("Augmented formula:\n{}", &augmented);
}
