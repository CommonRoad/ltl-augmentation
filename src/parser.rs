use crate::{formula::Formula, interval::Interval};

peg::parser! {
    pub grammar mltl_parser() for str {
        pub rule formula() -> Formula
            = precedence! {
                lhs:@ __ int:until_operator() __ rhs:(@) { Formula::until(lhs, int, rhs) }
                lhs:@ __ int:release_operator() __ rhs:(@) { Formula::release(lhs, int, rhs) }
                --
                int:finally_operator() __ sub:@ { Formula::finally(int, sub) }
                int:globally_operator() __ sub:@ { Formula::globally(int, sub) }
                --
                lhs:@ _ implies_operator() _ rhs:(@) { Formula::implies(lhs, rhs) }
                --
                lhs:(@) _ or_operator() _ rhs:@ { Formula::or(vec![lhs, rhs]) }
                --
                lhs:(@) _ and_operator() _ rhs:@ { Formula::and(vec![lhs, rhs]) }
                --
                not_operator() _ sub:@ { Formula::not(sub) }
                --
                ap:atomic_proposition() { ap }
                --
                "(" f:formula() ")" { f }
            }

        rule atomic_proposition() -> Formula
            = name:$(['a'..='z'] ['a'..='z' | 'A'..='Z' | '0'..='9']*) { Formula::AP(name.to_string()) }

        rule not_operator() = "!"

        rule and_operator() = "&"

        rule or_operator() = "|"

        rule implies_operator() = "->"

        rule until_operator() -> Interval = "U" i:interval() { i }

        rule release_operator() -> Interval = "R" i:interval() { i }

        rule finally_operator() -> Interval = "F" i:interval() { i }

        rule globally_operator() -> Interval = "G" i:interval() { i }

        rule interval() -> Interval
            = "[" start:number() _ "," _ end:number() "]" {?
                if start <= end {
                    Ok(Interval::from_endpoints(start, end))
                } else {
                    Err("invalid interval")
                }
            }

        rule number() -> u32
            = n:$(['0'..='9']+) {? n.parse().or(Err("u32")) }

        rule _ = quiet!{[' ' | '\n' | '\t']*}

        rule __ = quiet!{[' ' | '\n' | '\t']+}

    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn get_aps() -> (Formula, Formula, Formula) {
        let a = Formula::AP("a".to_string());
        let b = Formula::AP("b".to_string());
        let c = Formula::AP("c".to_string());
        (a, b, c)
    }

    #[test]
    fn test_parser() {
        use super::*;

        let formula = mltl_parser::formula("!a U[1, 2] !(b & F[0, 3] c)").unwrap();
        let (a, b, c) = get_aps();
        assert_eq!(
            formula,
            Formula::until(
                Formula::not(a),
                Interval::from_endpoints(1, 2),
                Formula::not(Formula::and(vec![
                    b,
                    Formula::finally(Interval::from_endpoints(0, 3), c)
                ]))
            )
        );
    }

    #[test]
    fn test_parser_associativity() {
        let (a, b, c) = get_aps();
        assert_eq!(
            mltl_parser::formula("a -> b -> c").unwrap(),
            Formula::implies(a, Formula::implies(b, c))
        );

        let (a, b, c) = get_aps();
        assert_eq!(
            mltl_parser::formula("a U[0, 1] b U[1, 2] c").unwrap(),
            Formula::until(
                a,
                Interval::from_endpoints(0, 1),
                Formula::until(b, Interval::from_endpoints(1, 2), c)
            )
        );
    }
}
