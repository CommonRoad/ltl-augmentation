use std::{cmp::Ordering, collections::BTreeMap};

use itertools::Itertools;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::sets::interval::Interval;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal<T, V> {
    values: BTreeMap<T, V>,
}

impl<T: Integer + Unsigned + Copy, V: Eq> Signal<T, V> {
    pub fn new() -> Self
    where
        V: Default,
    {
        Signal::uniform(Default::default())
    }

    pub fn uniform(v: V) -> Self {
        let mut values = BTreeMap::new();
        values.insert(T::zero(), v);
        Signal { values }
    }

    pub fn at(&self, time: T) -> &V {
        self.values
            .range(..=time)
            .next_back()
            .map(|(_, value)| value)
            .expect("Signal is never empty")
    }

    pub fn set(&mut self, interval: &Interval<T>, value: V)
    where
        V: Clone,
    {
        match interval {
            Interval::Bounded { lb, ub } => self.set_between(*lb, Some(*ub), value),
            Interval::Unbounded { lb } => self.set_between(*lb, None, value),
            Interval::Empty => (),
        }
    }

    fn set_between(&mut self, lb: T, ub: Option<T>, value: V)
    where
        V: Clone,
    {
        // Save the old value after the upper bound
        let succ_value = ub.map(|ub| self.at(ub + T::one()).clone());

        // Remove everything between lb and ub (None means infinity)
        self.values
            .retain(|time, _| time < &lb || ub.is_some_and(|ub| time > &ub));

        // If the old value after the upper bound is different from the new value, we need to insert a boundary
        if let (Some(ub), Some(succ_value)) = (ub, succ_value) {
            if succ_value != value {
                self.values.insert(ub + T::one(), succ_value);
            }
        }

        // Insert a boundary with the new value at the lower bound, if it is not set there already
        if lb == T::zero() || self.at(lb) != &value {
            self.values.insert(lb, value);
        }
    }

    pub fn map<F, W: Eq>(&self, op: F) -> Signal<T, W>
    where
        F: Fn(&V) -> W,
    {
        let values = self
            .values
            .iter()
            .map(|(time, value)| (*time, op(value)))
            .collect();
        Signal { values }.normalize()
    }

    // map_injective + combine_injective that omit normalization

    pub fn combine<F, W: Eq>(&self, other: &Signal<T, V>, op: F) -> Signal<T, W>
    where
        F: Fn(&V, &V) -> W,
    {
        // TODO: Could simplify this using merge
        let mut values = BTreeMap::new();

        let mut self_vals = self.values.iter().rev().peekable();
        let mut other_vals = other.values.iter().rev().peekable();

        // Since the last time in both iterators must be 0
        // and we always advance the iterator with the highest time,
        // the iterators will run dry simultaneously
        while self_vals.peek().is_some() && other_vals.peek().is_some() {
            let self_cur = self_vals.peek().expect("Peek was Some");
            let other_cur = other_vals.peek().expect("Peek was Some");

            let time = self_cur.0.max(other_cur.0);
            let value = op(self_cur.1, other_cur.1);

            values.insert(*time, value);

            // Advance the iterator with the largest time
            match self_cur.0.cmp(other_cur.0) {
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

    fn normalize(self) -> Signal<T, V> {
        let values = self
            .values
            .into_iter()
            .coalesce(|kv1, kv2| {
                if kv1.1 == kv2.1 {
                    Ok(kv1)
                } else {
                    Err((kv1, kv2))
                }
            })
            .collect();
        Signal { values }
    }
}

impl<T: Integer + Unsigned + Copy + SaturatingSub, V: Eq> Signal<T, V> {
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
            if !pred(&v1.1) {
                continue;
            }
            if let Some(v2) = it.peek() {
                result.push((
                    Interval::bounded(v1.0, v2.0.saturating_sub(&T::one())),
                    v1.1,
                ));
            } else {
                // Last element
                result.push((Interval::unbounded(v1.0), v1.1));
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
            if !pred(v1.1) {
                continue;
            }
            if let Some(v2) = it.peek() {
                result.push(Interval::bounded(*v1.0, v2.0.saturating_sub(&T::one())));
            } else {
                // Last element
                result.push(Interval::unbounded(*v1.0));
            }
        }
        result
    }

    pub fn intervals_where_eq(&self, v: &V) -> Vec<Interval<T>> {
        self.intervals_where(|vv| v == vv)
    }

    pub fn intervals(&self) -> Vec<(Interval<T>, V)>
    where
        V: Clone,
    {
        self.clone().into_intervals()
    }
}

impl<T: Integer + Unsigned + Copy, V: Default + Eq> Default for Signal<T, V> {
    fn default() -> Self {
        Signal::new()
    }
}

impl<T: Integer + Unsigned + Copy, V: Default + Eq + Clone> FromIterator<(Interval<T>, V)>
    for Signal<T, V>
{
    fn from_iter<I: IntoIterator<Item = (Interval<T>, V)>>(iter: I) -> Self {
        let mut signal = Signal::new();
        iter.into_iter().for_each(|(interval, value)| {
            signal.set(&interval, value);
        });
        signal
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_combine() {
        let mut signal1 = Signal::uniform(0);
        signal1.set(&Interval::bounded(1_u32, 2), 1);
        signal1.set(&Interval::bounded(3, 4), 3);
        signal1.set(&Interval::unbounded(5), 5);

        let mut signal2 = Signal::uniform(0);
        signal2.set(&Interval::singular(1_u32), -1);
        signal2.set(&Interval::bounded(2, 5), 20);
        signal2.set(&Interval::bounded(6, 10), 60);

        let combined_intervals = signal1.combine(&signal2, |a, b| a + b).into_intervals();
        assert_eq!(
            combined_intervals,
            vec![
                (Interval::bounded(0, 1), 0),
                (Interval::bounded(2, 2), 21),
                (Interval::bounded(3, 4), 23),
                (Interval::bounded(5, 5), 25),
                (Interval::bounded(6, 10), 65),
                (Interval::unbounded(11), 5)
            ]
        )
    }
}
