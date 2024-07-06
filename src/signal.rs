use std::{cmp::Ordering, collections::BTreeSet, hash::Hash, ops::Sub};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Interval<T> {
    Empty,
    Bounded { lb: T, ub: T },
    Unbounded { lb: T },
}

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

#[derive(Debug, Clone)]
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

impl<T: Copy + Sub<u32, Output = T>, V> Signal<T, V> {
    pub fn into_intervals(self) -> Vec<(Interval<T>, V)> {
        let mut result = Vec::with_capacity(self.values.len());
        let mut it = self.values.into_iter().peekable();
        while let Some(v1) = it.next() {
            if let Some(v2) = it.peek() {
                result.push((
                    Interval::Bounded {
                        lb: v1.time,
                        ub: v2.time - 1,
                    },
                    v1.value,
                ));
            } else {
                // Last element
                result.push((Interval::Unbounded { lb: v1.time }, v1.value));
            }
        }
        result
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
            time: 3_u32,
            value: 3,
        });
        signal1.values.insert(SignalValue {
            time: 5_u32,
            value: 5,
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
            time: 6_u32,
            value: 60,
        });

        let combined_intervals = signal1.combine(signal2, |a, b| a + b).into_intervals();
        assert_eq!(
            combined_intervals,
            vec![
                (Interval::Bounded { lb: 0, ub: 0 }, 0),
                (Interval::Bounded { lb: 1, ub: 1 }, 11),
                (Interval::Bounded { lb: 2, ub: 2 }, 21),
                (Interval::Bounded { lb: 3, ub: 4 }, 23),
                (Interval::Bounded { lb: 5, ub: 5 }, 25),
                (Interval::Unbounded { lb: 6 }, 65)
            ]
        )
    }
}
