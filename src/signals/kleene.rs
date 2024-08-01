use super::{signal::Signal, truth_values::Kleene};

pub type KleeneSignal<T> = Signal<T, Kleene>;
