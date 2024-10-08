use std::{cmp::Ordering, collections::BTreeMap};

use itertools::Itertools;

use crate::sets::interval::Interval;

use super::sets::interval_set::IntervalSet;

pub mod boolean;
pub mod knowledge;

pub type Time = u32;

pub trait Sequence<V> {
    fn new() -> Self
    where
        V: Default,
        Self: std::marker::Sized,
    {
        Self::uniform(Default::default())
    }

    fn uniform(v: V) -> Self;

    fn indicator(interval: &Interval, v: V, default: V) -> Self
    where
        V: Clone;

    fn at(&self, time: Time) -> &V;

    fn set(&mut self, interval: &Interval, value: V)
    where
        V: Clone;

    fn intervals_where<F>(&self, pred: F) -> Vec<Interval>
    where
        F: Fn(&V) -> bool;

    fn intervals_where_eq(&self, v: &V) -> Vec<Interval>
    where
        V: Eq,
    {
        self.intervals_where(|vv| v == vv)
    }

    fn interval_covering(&self, interval: &Interval) -> Vec<Interval>;

    fn refined_interval_covering(&self, other: &Self, interval: &Interval) -> Vec<Interval>;
}

pub trait Mappable<V, W> {
    fn map<F>(&self, op: F) -> impl Sequence<W>
    where
        F: Fn(&V) -> W;

    fn into_map<F>(self, op: F) -> impl Sequence<W>
    where
        F: Fn(V) -> W;
}

pub trait Combinable<V, U, W, S> {
    fn combine<F>(&self, other: &S, op: F) -> impl Sequence<W>
    where
        F: Fn(&V, &U) -> W;

    // fn into_combine<F>(&self, other: S, op: F) -> impl Sequence<W>
    // where
    //     F: Fn(V, U) -> W;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlainSequence<V> {
    values: BTreeMap<Time, V>,
}

impl<V> PlainSequence<V> {
    pub fn into_values(self) -> BTreeMap<Time, V> {
        self.values
    }

    fn set_between(&mut self, lb: Time, ub: Option<Time>, value: V)
    where
        V: Clone,
    {
        // Save the old value after the upper bound
        let succ_value = ub.map(|ub| self.at(ub).clone());

        // Remove everything between lb and ub (None means infinity)
        self.values
            .retain(|time, _| time < &lb || ub.is_some_and(|ub| time > &ub));

        // Insert a boundary at upper bound
        if let (Some(ub), Some(succ_value)) = (ub, succ_value) {
            self.values.insert(ub, succ_value);
        }

        // Insert a boundary with the new value at the lower bound
        self.values.insert(lb, value);
    }

    pub fn map<F, W>(&self, op: F) -> PlainSequence<W>
    where
        F: Fn(&V) -> W,
    {
        let values = self
            .values
            .iter()
            .map(|(time, value)| (*time, op(value)))
            .collect();
        PlainSequence { values }
    }

    pub fn into_map<F, W>(self, op: F) -> PlainSequence<W>
    where
        F: Fn(V) -> W,
    {
        let values = self
            .values
            .into_iter()
            .map(|(time, value)| (time, op(value)))
            .collect();
        PlainSequence { values }
    }

    pub fn combine<F, U, W>(&self, other: &PlainSequence<U>, op: F) -> PlainSequence<W>
    where
        F: Fn(&V, &U) -> W,
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

        PlainSequence { values }
    }

    fn iter_to_interval_covering<'a>(
        iter: impl Iterator<Item = &'a Time>,
        interval: &Interval,
    ) -> Vec<Interval> {
        iter.dedup()
            .copied()
            .map(Some)
            .chain(std::iter::once(None))
            .tuple_windows()
            .map(|(lb, ub)| match ub {
                Some(ub) => Interval::bounded(lb.unwrap(), ub.saturating_sub(1)),
                None => match interval.ub() {
                    Some(ub) => Interval::bounded(lb.unwrap(), *ub),
                    None => Interval::unbounded(lb.unwrap()),
                },
            })
            .collect()
    }
}

impl<V> Sequence<V> for PlainSequence<V> {
    fn uniform(v: V) -> Self {
        let mut values = BTreeMap::new();
        values.insert(0, v);
        PlainSequence { values }
    }

    fn indicator(interval: &Interval, v: V, default: V) -> Self
    where
        V: Clone,
    {
        let mut sequence = Self::uniform(default);
        sequence.set(interval, v);
        sequence
    }

    fn at(&self, time: Time) -> &V {
        self.values
            .range(..=time)
            .next_back()
            .expect("Sequence is never empty")
            .1
    }

    fn set(&mut self, interval: &Interval, value: V)
    where
        V: Clone,
    {
        match interval {
            Interval::Bounded { lb, ub } => self.set_between(*lb, Some(*ub + 1), value),
            Interval::Unbounded { lb } => self.set_between(*lb, None, value),
            Interval::Empty => (),
        }
    }

    fn intervals_where<F>(&self, pred: F) -> Vec<Interval>
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
                result.push(Interval::bounded(*v1.0, v2.0.saturating_sub(1)));
            } else {
                // Last element
                result.push(Interval::unbounded(*v1.0));
            }
        }
        result
    }

    fn interval_covering(&self, interval: &Interval) -> Vec<Interval> {
        if interval.is_empty() {
            return vec![];
        }
        let relevant_times = self.values.keys().filter(|t| interval.contains(t));
        Self::iter_to_interval_covering(
            std::iter::once(interval.lb().expect("interval should not be empty"))
                .chain(relevant_times),
            interval,
        )
    }

    fn refined_interval_covering(&self, other: &Self, interval: &Interval) -> Vec<Interval> {
        if interval.is_empty() {
            return vec![];
        }
        let relevant_times_self = self.values.keys().filter(|t| interval.contains(t));
        let relevant_times_other = other.values.keys().filter(|t| interval.contains(t));
        Self::iter_to_interval_covering(
            std::iter::once(interval.lb().expect("interval should not be empty"))
                .chain(relevant_times_self)
                .merge(relevant_times_other),
            interval,
        )
    }
}

impl<V, W> Mappable<V, W> for PlainSequence<V> {
    fn map<F>(&self, op: F) -> impl Sequence<W>
    where
        F: Fn(&V) -> W,
    {
        self.map(op)
    }

    fn into_map<F>(self, op: F) -> impl Sequence<W>
    where
        F: Fn(V) -> W,
    {
        self.into_map(op)
    }
}

impl<V, U, W> Combinable<V, U, W, PlainSequence<U>> for PlainSequence<V> {
    fn combine<F>(&self, other: &PlainSequence<U>, op: F) -> impl Sequence<W>
    where
        F: Fn(&V, &U) -> W,
    {
        self.combine(other, op)
    }
}

impl<T: Default + Clone> FromIterator<(Time, T)> for PlainSequence<T> {
    fn from_iter<I: IntoIterator<Item = (Time, T)>>(iter: I) -> Self {
        let mut seq = Self::new();
        for (time, value) in iter {
            seq.set(&Interval::singleton(time), value);
        }
        seq
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NormalizedSequence<V>(PlainSequence<V>);

impl<V: Eq> NormalizedSequence<V> {
    fn normalize(self) -> NormalizedSequence<V> {
        let values = self
            .0
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
        NormalizedSequence(PlainSequence { values })
    }

    fn set_between(&mut self, lb: Time, ub: Option<Time>, value: V)
    where
        V: Clone,
    {
        // Save the old value after the upper bound
        let succ_value = ub.map(|ub| self.at(ub).clone());

        // Remove everything between lb and ub (None means infinity)
        self.0
            .values
            .retain(|time, _| time < &lb || ub.is_some_and(|ub| time > &ub));

        // If the old value after the upper bound is different from the new value, we need to insert a boundary
        if let (Some(ub), Some(succ_value)) = (ub, succ_value) {
            if succ_value != value {
                self.0.values.insert(ub, succ_value);
            }
        }

        // Insert a boundary with the new value at the lower bound, if it is not set there already
        if lb == 0 || self.at(lb) != &value {
            self.0.values.insert(lb, value);
        }
    }

    pub fn map<F, W>(&self, op: F) -> NormalizedSequence<W>
    where
        F: Fn(&V) -> W,
        W: Eq,
    {
        NormalizedSequence(self.0.map(op)).normalize()
    }

    pub fn into_map<F, W>(self, op: F) -> NormalizedSequence<W>
    where
        F: Fn(V) -> W,
        W: Eq,
    {
        NormalizedSequence(self.0.into_map(op)).normalize()
    }

    pub fn combine<F, U, W>(&self, other: &NormalizedSequence<U>, op: F) -> NormalizedSequence<W>
    where
        F: Fn(&V, &U) -> W,
        W: Eq,
    {
        NormalizedSequence(self.0.combine(&other.0, op)).normalize()
    }

    pub fn last_change(&self) -> Time {
        *self
            .0
            .values
            .keys()
            .next_back()
            .expect("Sequence is never empty")
    }

    pub fn last_change_in(&self, time_steps: &IntervalSet) -> Option<Time> {
        let max = time_steps.max()?;
        Some(
            *self
                .0
                .values
                .range(..=max)
                .next_back()
                .expect("Signal is never empty")
                .0,
        )
    }
}

impl<V: Eq> Sequence<V> for NormalizedSequence<V> {
    fn uniform(v: V) -> Self {
        NormalizedSequence(PlainSequence::uniform(v))
    }

    fn indicator(interval: &Interval, v: V, default: V) -> Self
    where
        V: Clone,
    {
        let mut sequence = Self::uniform(default);
        sequence.set(interval, v);
        sequence
    }

    fn at(&self, time: Time) -> &V {
        self.0.at(time)
    }

    fn set(&mut self, interval: &Interval, value: V)
    where
        V: Clone,
    {
        match interval {
            Interval::Bounded { lb, ub } => self.set_between(*lb, Some(*ub + 1), value),
            Interval::Unbounded { lb } => self.set_between(*lb, None, value),
            Interval::Empty => (),
        }
    }

    fn intervals_where<F>(&self, pred: F) -> Vec<Interval>
    where
        F: Fn(&V) -> bool,
    {
        self.0.intervals_where(pred)
    }

    fn interval_covering(&self, interval: &Interval) -> Vec<Interval> {
        self.0.interval_covering(interval)
    }

    fn refined_interval_covering(&self, other: &Self, interval: &Interval) -> Vec<Interval> {
        self.0.refined_interval_covering(&other.0, interval)
    }
}

impl<V: Eq, W: Eq> Mappable<V, W> for NormalizedSequence<V> {
    fn map<F>(&self, op: F) -> impl Sequence<W>
    where
        F: Fn(&V) -> W,
    {
        self.map(op)
    }

    fn into_map<F>(self, op: F) -> impl Sequence<W>
    where
        F: Fn(V) -> W,
    {
        self.into_map(op)
    }
}

impl<V: Eq, U: Eq, W: Eq> Combinable<V, U, W, NormalizedSequence<U>> for NormalizedSequence<V> {
    fn combine<F>(&self, other: &NormalizedSequence<U>, op: F) -> impl Sequence<W>
    where
        F: Fn(&V, &U) -> W,
    {
        self.combine(other, op)
    }
}

impl<V: Eq> From<PlainSequence<V>> for NormalizedSequence<V> {
    fn from(sequence: PlainSequence<V>) -> Self {
        NormalizedSequence(sequence).normalize()
    }
}

impl<T: Default + Clone + Eq> FromIterator<(Time, T)> for NormalizedSequence<T> {
    fn from_iter<I: IntoIterator<Item = (Time, T)>>(iter: I) -> Self {
        NormalizedSequence(PlainSequence::from_iter(iter)).normalize()
    }
}
