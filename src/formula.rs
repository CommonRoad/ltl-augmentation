use super::interval::Interval;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Formula {
    // atomic proposition + constants
    AP(String),
    True,
    False,

    // propositional connectives
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),

    // temporal connectives
    Until(Box<Formula>, Interval, Box<Formula>),
    Release(Box<Formula>, Interval, Box<Formula>),
    Globally(Interval, Box<Formula>),
    Finally(Interval, Box<Formula>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NNFFormula {
    // atomic proposition + constants
    AP(String, bool),
    True,
    False,

    // propositional connectives
    And(Vec<NNFFormula>),
    Or(Vec<NNFFormula>),

    // temporal connectives
    Until(Box<NNFFormula>, Interval, Box<NNFFormula>),
    Release(Box<NNFFormula>, Interval, Box<NNFFormula>),
}

impl From<Formula> for NNFFormula {
    fn from(formula: Formula) -> NNFFormula {
        match formula {
            Formula::AP(name) => NNFFormula::AP(name, false),
            Formula::True => NNFFormula::True,
            Formula::False => NNFFormula::False,

            Formula::And(subs) => NNFFormula::And(subs.into_iter().map(|f| f.into()).collect()),
            Formula::Or(subs) => NNFFormula::Or(subs.into_iter().map(|f| f.into()).collect()),
            Formula::Implies(lhs, rhs) => {
                NNFFormula::Or(vec![Formula::Not(lhs).into(), (*rhs).into()])
            }

            Formula::Until(lhs, int, rhs) => NNFFormula::Until(lhs.into(), int, rhs.into()),
            Formula::Release(lhs, int, rhs) => NNFFormula::Release(lhs.into(), int, rhs.into()),

            Formula::Globally(int, sub) => {
                NNFFormula::Release(Box::new(NNFFormula::False), int, sub.into())
            }
            Formula::Finally(int, sub) => {
                NNFFormula::Until(Box::new(NNFFormula::True), int, sub.into())
            }

            Formula::Not(sub) => match *sub {
                Formula::AP(name) => NNFFormula::AP(name, true),
                Formula::True => NNFFormula::False,
                Formula::False => NNFFormula::True,

                Formula::And(subs) => NNFFormula::Or(
                    subs.into_iter()
                        .map(|f| Formula::Not(Box::new(f)).into())
                        .collect(),
                ),
                Formula::Or(subs) => NNFFormula::And(
                    subs.into_iter()
                        .map(|f| Formula::Not(Box::new(f)).into())
                        .collect(),
                ),
                Formula::Implies(lhs, rhs) => {
                    NNFFormula::And(vec![(*lhs).into(), Formula::Not(rhs).into()])
                }

                Formula::Until(lhs, int, rhs) => NNFFormula::Release(
                    Box::new(Formula::Not(lhs).into()),
                    int,
                    Box::new(Formula::Not(rhs).into()),
                ),
                Formula::Release(lhs, int, rhs) => NNFFormula::Until(
                    Box::new(Formula::Not(lhs).into()),
                    int,
                    Box::new(Formula::Not(rhs).into()),
                ),

                Formula::Globally(int, sub) => {
                    Formula::Finally(int, Box::new(Formula::Not(sub))).into()
                }
                Formula::Finally(int, sub) => {
                    Formula::Globally(int, Box::new(Formula::Not(sub))).into()
                }

                Formula::Not(sub) => (*sub).into(),
            },
        }
    }
}

impl From<Box<Formula>> for Box<NNFFormula> {
    fn from(formula: Box<Formula>) -> Box<NNFFormula> {
        Box::new(NNFFormula::from(*formula))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::interval::Interval;

    #[test]
    fn test_nnf_simple() {
        let formula = Formula::Not(Box::new(Formula::Until(
            Box::new(Formula::AP("a".to_string())),
            Interval::Range(3, 5),
            Box::new(Formula::Not(Box::new(Formula::AP("b".to_string())))),
        )));

        let nnf = NNFFormula::Release(
            Box::new(NNFFormula::AP("a".to_string(), true)),
            Interval::Range(3, 5),
            Box::new(NNFFormula::AP("b".to_string(), false)),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }

    #[test]
    fn test_nnf_complex() {
        let formula = Formula::Not(Box::new(Formula::Release(
            Box::new(Formula::Implies(
                Box::new(Formula::AP("a".to_string())),
                Box::new(Formula::AP("c".to_string())),
            )),
            Interval::Range(3, 5),
            Box::new(Formula::Finally(
                Interval::Range(0, 7),
                Box::new(Formula::Not(Box::new(Formula::AP("b".to_string())))),
            )),
        )));

        let nnf = NNFFormula::Until(
            Box::new(NNFFormula::And(vec![
                NNFFormula::AP("a".to_string(), false),
                NNFFormula::AP("c".to_string(), true),
            ])),
            Interval::Range(3, 5),
            Box::new(NNFFormula::Release(
                Box::new(NNFFormula::False),
                Interval::Range(0, 7),
                Box::new(NNFFormula::AP("b".to_string(), false)),
            )),
        );

        assert_eq!(NNFFormula::from(formula), nnf);
    }
}
