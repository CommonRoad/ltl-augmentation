use crate::formula::literal::Literal;
use crate::knowledge_graph::complexity_functions::ComplexityFunction;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct EquivalenceClass<C> {
    pub class: HashSet<Literal>,
    pub representative: Literal,
    representative_complexity: u32,
    complexity_function: std::marker::PhantomData<C>,
}

impl<C: ComplexityFunction> EquivalenceClass<C> {
    pub fn insert(&mut self, literal: Literal) {
        let new_complexity = C::complexity(&literal);
        if new_complexity < self.representative_complexity {
            self.representative = literal.clone();
            self.representative_complexity = new_complexity;
        }
        self.class.insert(literal);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Literal> {
        self.class.iter()
    }

    pub fn extend(&mut self, other: Self) {
        self.class.extend(other.class);
        if other.representative_complexity < self.representative_complexity {
            self.representative = other.representative;
            self.representative_complexity = other.representative_complexity;
        }
    }
}

impl<C: ComplexityFunction> From<Literal> for EquivalenceClass<C> {
    fn from(literal: Literal) -> Self {
        EquivalenceClass {
            representative_complexity: C::complexity(&literal),
            representative: literal.clone(),
            class: [literal].into(),
            complexity_function: std::marker::PhantomData,
        }
    }
}

impl<C: ComplexityFunction> TryFrom<HashSet<Literal>> for EquivalenceClass<C> {
    type Error = ();

    fn try_from(value: HashSet<Literal>) -> Result<Self, Self::Error> {
        let representative = value
            .iter()
            .min_by_key(|literal| C::complexity(literal))
            .ok_or(())?
            .clone();
        Ok(EquivalenceClass {
            representative_complexity: C::complexity(&representative),
            representative,
            class: value,
            complexity_function: std::marker::PhantomData,
        })
    }
}
