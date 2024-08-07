use std::{collections::HashMap, rc::Rc};

use crate::{
    sets::interval::Interval,
    signals::{signal::Signal, truth_values::Kleene},
    trace::Trace,
};

peg::parser! {
    pub grammar trace_parser() for str {
        pub rule trace() -> Trace<u32, Kleene>
            = aps:atomic_propositions() "\n" time_steps:time_steps() _ {?
                if time_steps.iter().all(|ts| ts.len() == aps.len()) {
                    let mut values = HashMap::new();
                    for (time, vals) in time_steps.into_iter().enumerate() {
                        let int = Interval::singleton(time as u32);
                        for (ap, value) in aps.iter().zip(vals) {
                            values.entry(Rc::clone(ap)).or_insert_with(|| Signal::uniform(Kleene::Unknown)).set(&int, value);
                        }
                    }
                    Ok(Trace::from(values))
                } else {
                    Err("Number of atomic propositions and time steps do not match")
                }
            }

        rule atomic_propositions() -> Vec<Rc<str>>
            = aps:(atomic_proposition() **<1,> " ") { aps }

        rule time_steps() -> Vec<Vec<Kleene>>
            = time_steps:(time_step() ** "\n") { time_steps }

        rule time_step() -> Vec<Kleene>
            = values:(kleene_value() **<1,> " ") { values }

        rule kleene_value() -> Kleene
            = "T" { Kleene::True }
            / "F" { Kleene::False }
            / "U" { Kleene::Unknown }

        rule atomic_proposition() -> Rc<str>
            = name:$(['a'..='z' | 'A'..='Z' | '0'..='9' | '_']+) {Rc::from(name) }

        rule _ = quiet!{[' ' | '\n' | '\t']*}
    }
}

#[cfg(test)]
mod tests {
    use rstest::*;

    use super::*;

    #[rstest]
    fn test_parser() {
        let trace = trace_parser::trace("a b c\nT F U\nT F F\n").unwrap();
        assert_eq!(
            trace,
            Trace::from(HashMap::from_iter([
                (
                    Rc::from("a"),
                    Signal::indicator(&Interval::bounded(0, 1), Kleene::True, Kleene::Unknown)
                ),
                (
                    Rc::from("b"),
                    Signal::indicator(&Interval::bounded(0, 1), Kleene::False, Kleene::Unknown)
                ),
                (
                    Rc::from("c"),
                    Signal::indicator(&Interval::singleton(1), Kleene::False, Kleene::Unknown)
                ),
            ]))
        );
    }
}
