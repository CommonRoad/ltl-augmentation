use pyo3::prelude::*;

mod augmentation;
mod formula;
mod knowledge;

#[pymodule]
fn mltl_simplification(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<knowledge::KnowledgeSequence>()?;
    m.add_class::<formula::Formula>()?;
    m.add_class::<augmentation::Augmenter>()?;
    Ok(())
}
