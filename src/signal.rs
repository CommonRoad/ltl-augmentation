use std::{cmp::Ordering, collections::BTreeSet, hash::Hash};

#[derive(Debug, Clone, Copy)]
struct SignalValue<T, V> {
    time: T,
    value: V,
}

impl<T: PartialEq, V> PartialEq for SignalValue<T, V> {
    fn eq(&self, other: &Self) -> bool {
        self.time == other.time
    }
}

impl<T: Eq, V> Eq for SignalValue<T, V> {}

impl<T: PartialOrd, V> PartialOrd for SignalValue<T, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.time.partial_cmp(&other.time)
    }
}

impl<T: Ord, V> Ord for SignalValue<T, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time.cmp(&other.time)
    }
}

impl<T: Hash, V> Hash for SignalValue<T, V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.time.hash(state);
    }
}

pub struct Signal<T, V> {
    values: BTreeSet<SignalValue<T, V>>,
}

impl<T: Ord + From<u32> + Copy, V: Default> Signal<T, V> {
    pub fn new() -> Self {
        let mut values = BTreeSet::new();
        values.insert(SignalValue {
            time: 0.into(),
            value: Default::default(),
        });
        Signal { values }
    }

    pub fn combine<F, W: Eq>(self, other: Signal<T, V>, op: F) -> Signal<T, W>
    where
        F: Fn(&V, &V) -> W,
    {
        let mut values = BTreeSet::new();

        let mut self_vals = self.values.into_iter();
        let mut self_cur = self_vals.next().expect("Signals are not empty");
        let mut self_prev: Option<SignalValue<T, V>> = None;
        let mut self_dry = false;

        let mut other_vals = other.values.into_iter();
        let mut other_cur = other_vals.next().expect("Signals are not empty");
        let mut other_prev: Option<SignalValue<T, V>> = None;
        let mut other_dry = false;

        while !self_dry || !other_dry {
            let cmp = self_cur.time.cmp(&other_cur.time);

            let signal_value = match (cmp, self_dry || other_dry) {
                (Ordering::Less, false) => SignalValue {
                    time: self_cur.time,
                    value: op(&self_cur.value, &other_prev.as_ref().expect("First time is 0 for both so we will advance both iterators before getting to this case").value),
                },
                (Ordering::Greater, false) => SignalValue {
                    time: other_cur.time,
                    value: op(&self_prev.as_ref().expect("First time is 0 for both so we will advance both iterators before getting to this case").value, &other_cur.value),
                },
                // If we have run one of the iterators dry, we always need to use the current value of this iterator
                _ => SignalValue {
                    time: if other_dry { self_cur.time } else { other_cur.time },
                    value: op(&self_cur.value, &other_cur.value),
                },
            };
            values.insert(signal_value);

            // Store condition for other, as we might change self_dry below
            let advance_other = matches!(cmp, Ordering::Greater | Ordering::Equal) || self_dry;
            if matches!(cmp, Ordering::Less | Ordering::Equal) || other_dry {
                if let Some(self_next) = self_vals.next() {
                    self_prev = Some(self_cur);
                    self_cur = self_next;
                } else {
                    self_dry = true;
                }
            }

            if advance_other {
                if let Some(other_next) = other_vals.next() {
                    other_prev = Some(other_cur);
                    other_cur = other_next;
                } else {
                    other_dry = true;
                }
            }
        }
        Signal { values }
    }
}

impl<T: Ord + From<u32> + Copy, V: Default> Default for Signal<T, V> {
    fn default() -> Self {
        Signal::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_combine() {
        let mut signal1 = Signal::new();
        signal1.values.insert(SignalValue {
            time: 1_u32,
            value: 1,
        });
        signal1.values.insert(SignalValue {
            time: 2_u32,
            value: 2,
        });
        signal1.values.insert(SignalValue {
            time: 3_u32,
            value: 3,
        });

        let mut signal2 = Signal::new();
        signal2.values.insert(SignalValue {
            time: 1_u32,
            value: 10,
        });
        signal2.values.insert(SignalValue {
            time: 2_u32,
            value: 20,
        });
        signal2.values.insert(SignalValue {
            time: 4_u32,
            value: 30,
        });

        let signal3 = signal1.combine(signal2, |a, b| a + b);
        let mut signal3 = signal3.values.into_iter();
        assert_eq!(signal3.next().unwrap().value, 0);
        assert_eq!(signal3.next().unwrap().value, 11);
        assert_eq!(signal3.next().unwrap().value, 22);
        assert_eq!(signal3.next().unwrap().value, 23);
        assert_eq!(signal3.next().unwrap().value, 33);
    }
}
