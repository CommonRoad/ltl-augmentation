use std::fmt::Display;
use std::sync::Arc;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AtomicProposition {
    pub name: Arc<str>,
    pub parameter: Arc<str>,
}

impl AtomicProposition {
    pub fn new(name: &str) -> Self {
        AtomicProposition {
            name: Arc::from(name),
            parameter: Arc::from(""),
        }
    }

    pub fn with_parameter(name: &str, parameter: &str) -> Self {
        AtomicProposition {
            name: Arc::from(name),
            parameter: Arc::from(parameter),
        }
    }
}

impl Display for AtomicProposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if self.parameter.len() > 0 {
            write!(f, "({})", self.parameter)?;
        }
        Ok(())
    }
}
