use crate::clean::formula::literal::Literal;

pub trait ComplexityFunction {
    fn complexity(literal: &Literal) -> u32;
}

#[derive(Debug, Clone)]
pub struct DefaultComplexityFunction;

impl ComplexityFunction for DefaultComplexityFunction {
    fn complexity(literal: &Literal) -> u32 {
        match literal {
            Literal::True => 0,
            Literal::False => 0,
            Literal::Positive(..) | Literal::Negative(..) => 1,
        }
    }
}
