use num::{Integer, Unsigned};

use super::{signal::Signal, truth_values::Kleene};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KleeneSignal<T> {
    over: Signal<T, bool>,
    under: Signal<T, bool>,
}

impl<T: Integer + Unsigned + Copy> KleeneSignal<T> {
    pub fn new() -> Self {
        KleeneSignal::uniform(Kleene::default())
    }

    pub fn from_approximations(over: Signal<T, bool>, under: Signal<T, bool>) -> Self {
        KleeneSignal { over, under }
    }

    pub fn uniform(k: Kleene) -> Self {
        KleeneSignal {
            over: Signal::uniform(k != Kleene::False),
            under: Signal::uniform(k != Kleene::True),
        }
    }

    pub fn over(&self) -> &Signal<T, bool> {
        &self.over
    }

    pub fn under(&self) -> &Signal<T, bool> {
        &self.under
    }
}

impl<T: Integer + Unsigned + Copy> Default for KleeneSignal<T> {
    fn default() -> Self {
        KleeneSignal::new()
    }
}

impl<T: Integer + Unsigned + Copy> From<Signal<T, Kleene>> for KleeneSignal<T> {
    fn from(signal: Signal<T, Kleene>) -> Self {
        let over = signal.map(|&k| k != Kleene::False);
        let under = signal.map(|&k| k == Kleene::True);
        KleeneSignal { over, under }
    }
}

impl<T: Integer + Unsigned + Copy> From<KleeneSignal<T>> for Signal<T, Kleene> {
    fn from(signal: KleeneSignal<T>) -> Self {
        signal.over.combine(&signal.under, |&o, &u| match (o, u) {
            (true, true) => Kleene::True,
            (false, false) => Kleene::False,
            (true, false) => Kleene::Unknown,
            (false, true) => {
                unreachable!("Overapproximation is always more true than underapproximation")
            }
        })
    }
}
