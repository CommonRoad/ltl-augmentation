use std::{collections::HashMap, fmt::Display};

use pyo3::{exceptions::PyValueError, prelude::*};

use crate::clean::{
    formula::{nnf::NNFFormula, parser::mltl_parser},
    sequence::Time,
    sets::interval::Interval,
};

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

    #[pyo3(signature = (end, start=0))]
    fn relevant_aps(&self, end: Time, start: Time) -> HashMap<Time, Vec<String>> {
        let interval = Interval::bounded(start, end).into();
        let mut aps_with_time = HashMap::new();
        for (ap, time_steps) in self.0.collect_aps_with_time() {
            time_steps
                .intersect(&interval)
                .get_intervals()
                .into_iter()
                .flatten()
                .for_each(|time| {
                    aps_with_time
                        .entry(time)
                        .or_insert_with(Vec::new)
                        .push(ap.name.to_string());
                });
        }
        aps_with_time
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
