use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::AtomicProposition,
    signals::{signal::Signal, truth_values::Kleene},
    trace::Trace,
};

// if key is true, all values in the first vector are true
// if key is false, all values in the second vector are true
type Implications<T> =
    HashMap<Rc<str>, Signal<T, (Vec<AtomicProposition>, Vec<AtomicProposition>)>>;

struct Equivalence {
    class: HashSet<AtomicProposition>,
    representative: AtomicProposition,
}

fn enrich_trace<T>(mut trace: Trace<T, Kleene>, implications: &Implications<T>) -> Trace<T, Kleene>
where
    T: Integer + Unsigned + Copy + SaturatingSub,
{
    loop {
        let mut new_trace = trace.clone();
        for (ap, signal) in trace.get_signals() {
            let implied = implications.get(ap);
            if implied.is_none() {
                continue;
            }
            let implied = implied.unwrap();
            let intervals = signal.get_refined_intervals(implied);
            for interval in &intervals {
                let lb = *interval.lb().expect("interval should not be empty");
                let implied_aps = match signal.at(lb) {
                    Kleene::True => &implied.at(lb).0,
                    Kleene::False => &implied.at(lb).1,
                    Kleene::Unknown => &vec![],
                };
                for ap in implied_aps.iter() {
                    new_trace.set_ap_interval(ap.name.clone(), interval, (!ap.negated).into());
                }
            }
        }
        if new_trace == trace {
            return new_trace;
        }
        trace = new_trace;
    }
}

#[cfg(test)]
mod tests {
    use crate::{sets::interval::Interval, trace_parser::trace_parser};

    use super::*;

    #[test]
    fn test_enrich() {
        let trace =
            trace_parser::trace(include_str!("../example_trace.txt")).expect("Syntax is correct");
        let implications = HashMap::from([(
            Rc::from("oar"),
            Signal::indicator(
                &Interval::bounded(0, 5),
                (
                    vec![AtomicProposition {
                        name: Rc::from("rl"),
                        negated: true,
                    }],
                    vec![],
                ),
                (vec![], vec![]),
            ),
        )]);
        let enriched = enrich_trace(trace, &implications);
        println!("{:?}", enriched);
    }
}
