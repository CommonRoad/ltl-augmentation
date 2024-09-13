use crate::clean::formula::atomic_proposition::AtomicProposition;
use crate::clean::formula::ltl::Formula;
use crate::clean::sets::interval::Interval;

peg::parser! {
    pub grammar mltl_parser() for str {
        pub rule formula() -> Formula
            = _ f:formula_precedence() _ { f }

        rule formula_precedence() -> Formula
            = precedence! {
                lhs:@ __ int:until_operator() __ rhs:(@) { Formula::until(lhs, int, rhs) }
                lhs:@ __ int:release_operator() __ rhs:(@) { Formula::release(lhs, int, rhs) }
                --
                int:finally_operator() __ sub:@ {
                    if int.is_singleton() {
                        Formula::next(*int.lb().unwrap(), sub)
                    } else {
                        Formula::finally(int, sub)
                    }
                }
                int:globally_operator() __ sub:@ {
                    if int.is_singleton() {
                        Formula::next(*int.lb().unwrap(), sub)
                    } else {
                        Formula::globally(int, sub)
                    }
                }
                time:next_operator() __ sub:@ { Formula::next(time, sub) }
                --
                lhs:@ _ implies_operator() _ rhs:(@) { Formula::implies(lhs, rhs) }
                --
                lhs:(@) _ or_operator() _ rhs:@ { Formula::or([lhs, rhs]) }
                --
                lhs:(@) _ and_operator() _ rhs:@ { Formula::and([lhs, rhs]) }
                --
                not_operator() _ sub:@ { Formula::negated(sub) }
                --
                atom:atomic_formula() { atom }
                --
                "(" f:formula() ")" { f }
            }

        rule atomic_formula() -> Formula
            = f:(true_formula() / false_formula() / atomic_proposition()) { f }

        rule true_formula() -> Formula
            = ("True" / "true") { Formula::True }

        rule false_formula() -> Formula
            = ("False" / "false") { Formula::False }

        rule atomic_proposition() -> Formula
            = name:$(['a'..='z' | 'A'..='Z' | '0'..='9'] ['a'..='z' | 'A'..='Z' | '0'..='9' | '_']*) param:parameter()? {
                match param {
                    Some(param) => Formula::AP(AtomicProposition::with_parameter(name, param)),
                    None => Formula::AP(AtomicProposition::new(name))
                }
            }

        rule parameter() -> &'input str
            = "(" param:$(['a'..='z' | 'A'..='Z' | '0'..='9' | '_']*) ")" { param }

        rule not_operator() = "!"

        rule and_operator() = "&"

        rule or_operator() = "|"

        rule implies_operator() = "->"

        rule until_operator() -> Interval = "U" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule release_operator() -> Interval = "R" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule finally_operator() -> Interval = "F" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule globally_operator() -> Interval = "G" i:interval()? { i.unwrap_or_else(|| Interval::unbounded(0)) }

        rule next_operator() -> u32 = "X" t:singleton()? { t.unwrap_or(1) }

        rule interval() -> Interval
            = unbounded_interval() / bounded_interval() / singleton_interval() / expected!("Bounded, unbounded, or singleton interval")

        rule bounded_interval() -> Interval
            = "[" lb:number() _ "," _ ub:number() "]" {?
                if lb <= ub {
                    Ok(Interval::bounded(lb, ub))
                } else {
                    Err("Invalid bounded interval: Upper bound is smaller than lower bound")
                }
            }

        rule unbounded_interval() -> Interval
            = "[" lb:number() _ "," _ ("*" / "inf") "]" { Interval::unbounded(lb) }

        rule singleton_interval() -> Interval
            = x:singleton() { Interval::singleton(x) }

        rule singleton() -> u32
            = "[" x:number() "]" { x }

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
    fn aps() -> [Formula; 4] {
        let a = Formula::AP(AtomicProposition::new("a"));
        let b = Formula::AP(AtomicProposition::new("b"));
        let c = Formula::AP(AtomicProposition::new("c"));
        let d_param = Formula::AP(AtomicProposition::with_parameter("d", "42"));
        [a, b, c, d_param]
    }

    #[rstest]
    fn test_parser(aps: [Formula; 4]) {
        let [a, b, c, ..] = aps;

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
    fn test_parser_associativity(aps: [Formula; 4]) {
        let [a, b, c, ..] = aps;

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

    #[rstest]
    fn test_parser_parameter(aps: [Formula; 4]) {
        let [a, b, _, d_param] = aps;

        assert_eq!(
            mltl_parser::formula("a R b -> d(42)").unwrap(),
            Formula::release(
                a.clone(),
                Interval::unbounded(0),
                Formula::implies(b.clone(), d_param.clone())
            )
        );
    }
}
