use std::{collections::HashMap, fmt::Display};

use pyo3::{exceptions::PyValueError, prelude::*};

use crate::clean::{
    formula::{
        atomic_proposition::AtomicProposition, literal::Literal, nnf::NNFFormula,
        parser::mltl_parser,
    },
    sequence::Time,
    sets::interval::Interval,
};

#[pyclass]
#[derive(Clone)]
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

    #[staticmethod]
    fn true_formula() -> Self {
        Formula(NNFFormula::Literal(Literal::True))
    }

    #[staticmethod]
    fn false_formula() -> Self {
        Formula(NNFFormula::Literal(Literal::False))
    }

    #[staticmethod]
    #[pyo3(signature = (name, parameter=None))]
    fn ap(name: &str, parameter: Option<&str>) -> Self {
        Formula(NNFFormula::Literal(Literal::Positive(match parameter {
            Some(parameter) => AtomicProposition::with_parameter(name, parameter),
            None => AtomicProposition::new(name),
        })))
    }

    #[staticmethod]
    fn negation(formula: &Formula) -> Self {
        Formula(formula.0.clone().negated())
    }

    #[staticmethod]
    fn conjunction(formulas: Vec<Bound<'_, Formula>>) -> Self {
        Formula(NNFFormula::and(
            formulas.iter().map(|f| f.borrow().0.clone()),
        ))
    }

    #[staticmethod]
    fn disjunction(formulas: Vec<Bound<'_, Formula>>) -> Self {
        Formula(NNFFormula::or(
            formulas.iter().map(|f| f.borrow().0.clone()),
        ))
    }

    #[staticmethod]
    fn implication(lhs: &Formula, rhs: &Formula) -> Self {
        Formula(NNFFormula::implies(lhs.0.clone(), rhs.0.clone()))
    }

    #[staticmethod]
    #[pyo3(signature = (formula, time=1))]
    fn next(formula: &Formula, time: Time) -> Self {
        Formula(NNFFormula::next(time, formula.0.clone()))
    }

    #[staticmethod]
    #[pyo3(signature = (formula, start=0, end=None))]
    fn always(formula: &Formula, start: Time, end: Option<Time>) -> Self {
        let interval = match end {
            Some(end) => Interval::bounded(start, end),
            None => Interval::unbounded(start),
        };
        Formula(NNFFormula::globally(interval, formula.0.clone()))
    }

    #[staticmethod]
    #[pyo3(signature = (formula, start=0, end=None))]
    fn eventually(formula: &Formula, start: Time, end: Option<Time>) -> Self {
        let interval = match end {
            Some(end) => Interval::bounded(start, end),
            None => Interval::unbounded(start),
        };
        Formula(NNFFormula::finally(interval, formula.0.clone()))
    }

    #[staticmethod]
    #[pyo3(signature = (lhs, rhs, start=0, end=None))]
    fn until(lhs: &Formula, rhs: &Formula, start: Time, end: Option<Time>) -> Self {
        let interval = match end {
            Some(end) => Interval::bounded(start, end),
            None => Interval::unbounded(start),
        };
        Formula(NNFFormula::until(lhs.0.clone(), interval, rhs.0.clone()))
    }

    #[staticmethod]
    #[pyo3(signature = (lhs, rhs, start=0, end=None))]
    fn release(lhs: &Formula, rhs: &Formula, start: Time, end: Option<Time>) -> Self {
        let interval = match end {
            Some(end) => Interval::bounded(start, end),
            None => Interval::unbounded(start),
        };
        Formula(NNFFormula::release(lhs.0.clone(), interval, rhs.0.clone()))
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
                        .push(format!("{}", ap));
                });
        }
        aps_with_time
    }

    fn split_at_top_level_conjunction(&self) -> Vec<Formula> {
        match &self.0 {
            NNFFormula::And(subs) => subs.iter().cloned().map(Formula).collect(),
            _ => vec![self.clone()],
        }
    }

    fn format_as_string(&self, format_literal: Bound<'_, PyAny>) -> PyResult<String> {
        self.0
            .clone()
            .remove_timed_until()
            .format_as_string(&|literal| match literal {
                Literal::True => format_literal
                    .call1(("true", None::<&str>))?
                    .extract::<String>(),
                Literal::False => format_literal
                    .call1(("false", None::<&str>))?
                    .extract::<String>(),
                Literal::Positive(AtomicProposition { name, parameter })
                | Literal::Negative(AtomicProposition { name, parameter }) => format_literal
                    .call1((name.as_ref(), Some(parameter.as_ref())))?
                    .extract::<String>(),
            })
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
