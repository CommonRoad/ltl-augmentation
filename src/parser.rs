use std::rc::Rc;

use crate::{
    formula::{AtomicProposition, Formula},
    sets::interval::Interval,
};

peg::parser! {
    pub grammar mltl_parser() for str {
        pub rule formula() -> Formula<u32>
            = precedence! {
                lhs:@ __ int:until_operator() __ rhs:(@) { Formula::until(lhs, int, rhs) }
                lhs:@ __ int:release_operator() __ rhs:(@) { Formula::release(lhs, int, rhs) }
                --
                int:finally_operator() __ sub:@ { Formula::finally(int, sub) }
                int:globally_operator() __ sub:@ { Formula::globally(int, sub) }
                --
                lhs:@ _ implies_operator() _ rhs:(@) { Formula::implies(lhs, rhs) }
                --
                lhs:(@) _ or_operator() _ rhs:@ { Formula::or([lhs, rhs]) }
                --
                lhs:(@) _ and_operator() _ rhs:@ { Formula::and([lhs, rhs]) }
                --
                not_operator() _ sub:@ { Formula::negated(sub) }
                --
                ap:atomic_proposition() { Formula::AP(ap) }
                --
                "(" f:formula() ")" { f }
            }

        rule atomic_proposition() -> AtomicProposition
            = name:$(['a'..='z' | 'A'..='Z' | '0'..='9' | '_']+) { AtomicProposition { name: Rc::from(name), negated: false } }

        rule not_operator() = "!"

        rule and_operator() = "&"

        rule or_operator() = "|"

        rule implies_operator() = "->"

        rule until_operator() -> Interval<u32> = "U" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule release_operator() -> Interval<u32> = "R" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule finally_operator() -> Interval<u32> = "F" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule globally_operator() -> Interval<u32> = "G" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule interval() -> Interval<u32>
            = unbounded_interval() / bounded_interval() / expected!("Bounded or unbounded interval")

        rule bounded_interval() -> Interval<u32>
            = "[" lb:number() _ "," _ ub:number() "]" {?
                if lb <= ub {
                    Ok(Interval::bounded(lb, ub))
                } else {
                    Err("Invalid bounded interval: Upper bound is smaller than lower bound")
                }
            }

        rule unbounded_interval() -> Interval<u32>
            = "[" lb:number() _ "," _ ("*" / "inf") "]" { Interval::unbounded(lb) }

        rule number() -> u32
            = n:$(['0'..='9']+) {? n.parse().or(Err("u32")) }

        rule _ = quiet!{[' ' | '\n' | '\t']*}

        rule __ = quiet!{[' ' | '\n' | '\t']+}

    }
}

#[cfg(test)]
mod tests {
    use rstest::*;

    use super::*;

    #[fixture]
    fn aps<T>() -> (Formula<T>, Formula<T>, Formula<T>) {
        let a = Formula::AP(AtomicProposition {
            name: Rc::from("a"),
            negated: false,
        });
        let b = Formula::AP(AtomicProposition {
            name: Rc::from("b"),
            negated: false,
        });
        let c = Formula::AP(AtomicProposition {
            name: Rc::from("c"),
            negated: false,
        });
        (a, b, c)
    }

    #[rstest]
    fn test_parser(aps: (Formula<u32>, Formula<u32>, Formula<u32>)) {
        let (a, b, c) = aps;

        let formula = mltl_parser::formula("!a U[1, 2] !(b & F[0, 3] c)").unwrap();
        assert_eq!(
            formula,
            Formula::until(
                Formula::negated(a),
                Interval::bounded(1, 2),
                Formula::negated(Formula::and(vec![
                    b,
                    Formula::finally(Interval::bounded(0, 3), c)
                ]))
            )
        );
    }

    #[rstest]
    fn test_parser_associativity(aps: (Formula<u32>, Formula<u32>, Formula<u32>)) {
        let (a, b, c) = aps;

        assert_eq!(
            mltl_parser::formula("a -> b -> c").unwrap(),
            Formula::implies(a.clone(), Formula::implies(b.clone(), c.clone()))
        );

        assert_eq!(
            mltl_parser::formula("a U[0, 1] b U[1, 2] c").unwrap(),
            Formula::until(
                a,
                Interval::bounded(0, 1),
                Formula::until(b, Interval::bounded(1, 2), c)
            )
        );
    }
}
