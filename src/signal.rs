use std::{cmp::Ordering, collections::BTreeSet, hash::Hash};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Interval<T> {
    Empty,
    Bounded { lb: T, ub: T },
    Unbounded { lb: T },
}

impl<T: Ord> Interval<T> {
    pub fn empty() -> Self {
        Interval::Empty
    }

    pub fn bounded(lb: T, ub: T) -> Self {
        if lb > ub {
            Interval::Empty
        } else {
            Interval::Bounded { lb, ub }
        }
    }

    pub fn unbounded(lb: T) -> Self {
        Interval::Unbounded { lb }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Interval::Empty)
    }
}

impl<T: Integer + Unsigned + Copy> Interval<T> {
    pub fn intersect(&self, other: &Self) -> Self {
        match (self, other) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (Interval::Bounded { lb: lb1, ub: ub1 }, Interval::Bounded { lb: lb2, ub: ub2 }) => {
                Interval::bounded(*lb1.max(lb2), *ub1.min(ub2))
            }
            (Interval::Bounded { lb: lb1, ub }, Interval::Unbounded { lb: lb2 })
            | (Interval::Unbounded { lb: lb1 }, Interval::Bounded { lb: lb2, ub }) => {
                Interval::bounded(*lb1.max(lb2), *ub)
            }
            (Interval::Unbounded { lb: lb1 }, Interval::Unbounded { lb: lb2 }) => {
                Interval::Unbounded { lb: *lb1.max(lb2) }
            }
        }
    }
}

impl<T: Ord> Default for Interval<T> {
    fn default() -> Self {
        Interval::empty()
    }
}

impl<T: Integer + Unsigned + Copy> std::ops::Add for Interval<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (Interval::Bounded { lb: lb1, ub: ub1 }, Interval::Bounded { lb: lb2, ub: ub2 }) => {
                Interval::bounded(lb1 + lb2, ub1 + ub2)
            }
            (Interval::Bounded { lb: lb1, .. }, Interval::Unbounded { lb: lb2 })
            | (Interval::Unbounded { lb: lb1 }, Interval::Bounded { lb: lb2, .. })
            | (Interval::Unbounded { lb: lb1 }, Interval::Unbounded { lb: lb2 }) => {
                Interval::unbounded(lb1 + lb2)
            }
        }
    }
}

impl<T: Integer + Unsigned + SaturatingSub + Copy> std::ops::Sub for Interval<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) | (_, Interval::Empty) => Interval::empty(),
            (
                Interval::Bounded {
                    lb: lb_min,
                    ub: ub_min,
                },
                Interval::Bounded {
                    lb: lb_sub,
                    ub: ub_sub,
                },
            ) => {
                if ub_min >= lb_sub {
                    Interval::bounded(lb_min.saturating_sub(&ub_sub), ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { ub: ub_min, .. }, Interval::Unbounded { lb: lb_sub }) => {
                if ub_min >= lb_sub {
                    Interval::bounded(T::zero(), ub_min - lb_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { ub: ub_sub, .. }) => {
                Interval::unbounded(lb_min.saturating_sub(&ub_sub))
            }
            (Interval::Unbounded { .. }, Interval::Unbounded { .. }) => {
                Interval::unbounded(T::zero())
            }
        }
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub> Interval<T> {
    pub fn minkowski_difference(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Interval::Empty, _) => Interval::empty(),
            (_, Interval::Empty) => Interval::unbounded(T::zero()),
            (
                Interval::Bounded {
                    lb: lb_min,
                    ub: ub_min,
                },
                Interval::Bounded {
                    lb: lb_sub,
                    ub: ub_sub,
                },
            ) => {
                if ub_min >= ub_sub {
                    Interval::bounded(lb_min.saturating_sub(&lb_sub), ub_min - ub_sub)
                } else {
                    Interval::empty()
                }
            }
            (Interval::Bounded { .. }, Interval::Unbounded { .. }) => Interval::empty(),
            (Interval::Unbounded { lb: lb_min }, Interval::Bounded { lb: lb_sub, .. })
            | (Interval::Unbounded { lb: lb_min }, Interval::Unbounded { lb: lb_sub }) => {
                Interval::unbounded(lb_min.saturating_sub(&lb_sub))
            }
        }
    }
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

impl<T: Integer + Unsigned + Copy, V: Default> Signal<T, V> {
    pub fn new() -> Self {
        Signal::uniform(Default::default())
    }
}

impl<T: Integer + Unsigned + Copy, V> Signal<T, V> {
    pub fn uniform(v: V) -> Self {
        let mut values = BTreeSet::new();
        values.insert(SignalValue {
            time: T::zero(),
            value: v,
        });
        Signal { values }
    }

    pub fn map<F, W: Eq>(&self, op: F) -> Signal<T, W>
    where
        F: Fn(&V) -> W,
    {
        let values = self
            .values
            .iter()
            .map(|SignalValue { time, value }| SignalValue {
                time: *time,
                value: op(value),
            })
            .collect();
        Signal { values }.normalize()
    }

    // map_injective + combine_injective that omit normalization

    pub fn combine<F, W: Eq>(&self, other: &Signal<T, V>, op: F) -> Signal<T, W>
    where
        F: Fn(&V, &V) -> W,
    {
        let mut values = BTreeSet::new();

        let mut self_vals = self.values.iter().rev().peekable();
        let mut other_vals = other.values.iter().rev().peekable();

        // Since the last time in both iterators must be 0
        // and we always advance the iterator with the highest time,
        // the iterators will run dry simultaneously
        while self_vals.peek().is_some() && other_vals.peek().is_some() {
            let self_cur = self_vals.peek().expect("Peek was Some");
            let other_cur = other_vals.peek().expect("Peek was Some");

            let time = self_cur.time.max(other_cur.time);
            let value = op(&self_cur.value, &other_cur.value);

            values.insert(SignalValue { time, value });

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

        Signal { values }.normalize()
    }
}

impl<T: Integer + Unsigned + Copy, V: Eq> Signal<T, V> {
    fn normalize(self) -> Signal<T, V> {
        let values = self
            .values
            .into_iter()
            .coalesce(|sv1, sv2| {
                if sv1.value == sv2.value {
                    Ok(sv1)
                } else {
                    Err((sv1, sv2))
                }
            })
            .collect();
        Signal { values }
    }
}

impl<T: Integer + Unsigned + SaturatingSub + Copy, V> Signal<T, V> {
    pub fn into_intervals(self) -> Vec<(Interval<T>, V)> {
        self.into_intervals_where(|_| true)
    }

    pub fn into_intervals_where<F>(self, pred: F) -> Vec<(Interval<T>, V)>
    where
        F: Fn(&V) -> bool,
    {
        let mut result = Vec::with_capacity(self.values.len());
        let mut it = self.values.into_iter().peekable();
        while let Some(v1) = it.next() {
            if !pred(&v1.value) {
                continue;
            }
            if let Some(v2) = it.peek() {
                result.push((
                    Interval::Bounded {
                        lb: v1.time,
                        ub: v2.time.saturating_sub(&T::one()),
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

    pub fn intervals_where<F>(&self, pred: F) -> Vec<Interval<T>>
    where
        F: Fn(&V) -> bool,
    {
        let mut result = Vec::with_capacity(self.values.len());
        let mut it = self.values.iter().peekable();
        while let Some(v1) = it.next() {
            if !pred(&v1.value) {
                continue;
            }
            if let Some(v2) = it.peek() {
                result.push(Interval::Bounded {
                    lb: v1.time,
                    ub: v2.time.saturating_sub(&T::one()),
                });
            } else {
                // Last element
                result.push(Interval::Unbounded { lb: v1.time });
            }
        }
        result
    }
}

impl<T: Integer + Unsigned + SaturatingSub + Copy, V: Eq> Signal<T, V> {
    pub fn intervals_where_eq(&self, v: &V) -> Vec<Interval<T>> {
        self.intervals_where(|vv| v == vv)
    }
}

impl<T: Integer + Unsigned + SaturatingSub + Copy, V: Clone> Signal<T, V> {
    pub fn intervals(&self) -> Vec<(Interval<T>, V)> {
        self.clone().into_intervals()
    }
}

impl<T: Integer + Unsigned + Copy, V: Default> Default for Signal<T, V> {
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

        let combined_intervals = signal1.combine(&signal2, |a, b| a + b).into_intervals();
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
