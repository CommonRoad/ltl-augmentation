use pyo3::{exceptions::PyValueError, prelude::*};

use crate::clean::{
    augmentation,
    formula::{nnf::NNFFormula, parser::mltl_parser},
};

#[pyclass]
pub struct Augmenter {
    knowledge: usize,
}

// #[pymethods]
// impl Augmenter {
//     #[new]
//     fn new(knowledge: Py<KnowledgeSequence>) -> Self {
//         knowledge.
//         Augmenter { knowledge }
//     }
// }
