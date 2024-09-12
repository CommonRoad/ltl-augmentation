use std::fmt::Display;

use pyo3::{exceptions::PyValueError, prelude::*};

use crate::clean::formula::{nnf::NNFFormula, parser::mltl_parser};

#[pyclass]
pub struct Formula(pub NNFFormula);

#[pymethods]
impl Formula {
    #[new]
    fn new(formula_string: &str) -> PyResult<Self> {
        let formula = mltl_parser::formula(formula_string)
            .map_err(|err| PyValueError::new_err(format!("{}", err)))?
            .into();
        Ok(Formula(formula))
    }

    fn __str__(&self) -> PyResult<String> {
        Ok(format!("{}", self))
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.0))
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
