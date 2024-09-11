use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AtomicProposition {
    pub name: Rc<str>,
    pub negated: bool,
}

impl Display for AtomicProposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.negated {
            write!(f, "¬{}", self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}
