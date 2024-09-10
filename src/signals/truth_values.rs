pub trait TruthValue {
    fn top() -> Self;
    fn bot() -> Self;
}

impl TruthValue for bool {
    fn top() -> Self {
        true
    }

    fn bot() -> Self {
        false
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kleene {
    True,
    #[default]
    Unknown,
    False,
}

impl From<bool> for Kleene {
    fn from(b: bool) -> Self {
        if b {
            Kleene::True
        } else {
            Kleene::False
        }
    }
}

impl TruthValue for Kleene {
    fn top() -> Self {
        Kleene::True
    }

    fn bot() -> Self {
        Kleene::False
    }
}
