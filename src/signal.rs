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

        let mut self_vals = self.values.into_iter().rev().peekable();
        let mut other_vals = other.values.into_iter().rev().peekable();

        let mut candidate: Option<SignalValue<T, W>> = None;

        // Since the last time in both iterators must be 0
        // and we always advance the iterator with the highest time,
        // the iterators will run dry simultaneously
        while self_vals.peek().is_some() && other_vals.peek().is_some() {
            let self_cur = self_vals.peek().expect("Peek was Some");
            let other_cur = other_vals.peek().expect("Peek was Some");

            let time = self_cur.time.max(other_cur.time);
            let value = op(&self_cur.value, &other_cur.value);

            // Insert the current candidate if the value changed
            if candidate
                .as_ref()
                .is_some_and(|sig_val| sig_val.value != value)
            {
                values.insert(candidate.expect("We checked for Some above"));
            }
            candidate = Some(SignalValue { time, value });

            // Advance the iterator with the largest time
            match self_cur.time.cmp(&other_cur.time) {
                Ordering::Less => {
                    other_vals.next();
                }
                Ordering::Equal => {
                    self_vals.next();
                    other_vals.next();
                }
                Ordering::Greater => {
                    self_vals.next();
                }
            }
        }
        assert!(self_vals.peek().is_none() && other_vals.peek().is_none());

        if let Some(sig_val) = candidate {
            values.insert(sig_val);
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
            value: -1,
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
                (Interval::Bounded { lb: 0, ub: 1 }, 0),
                (Interval::Bounded { lb: 2, ub: 2 }, 21),
                (Interval::Bounded { lb: 3, ub: 4 }, 23),
                (Interval::Bounded { lb: 5, ub: 5 }, 25),
                (Interval::Unbounded { lb: 6 }, 65)
            ]
        )
    }
}
