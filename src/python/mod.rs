use pyo3::prelude::*;

mod augmentation;
mod formula;
mod knowledge;

#[pymodule]
fn ltl_augmentation(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<knowledge::KnowledgeSequence>()?;
    m.add_class::<formula::Formula>()?;
    m.add_class::<augmentation::Augmenter>()?;
    Ok(())
}
