use pyo3::prelude::*;

use crate::clean::augmentation;

use super::{formula::Formula, knowledge::KnowledgeSequence};

#[pyclass]
pub struct Augmenter(pub augmentation::Augmenter);

#[pymethods]
impl Augmenter {
    #[new]
    fn new(knowledge: Bound<'_, KnowledgeSequence>) -> Self {
        let rust_knowledge = knowledge.borrow().0.clone();
        Augmenter(augmentation::Augmenter::new(rust_knowledge))
    }

    fn augment(&self, formula: Bound<'_, Formula>) -> Formula {
        Formula(self.0.augment(&formula.borrow().0))
    }
}
