use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    hash::Hash,
    iter::Peekable,
};

use itertools::{iproduct, Itertools};
use num::{Integer, Unsigned};

use crate::formula::NNFFormula;

type Clause<T> = BTreeSet<T>;
type ClauseSet<T> = HashSet<Clause<T>>;

pub struct MinDNF<T>(std::marker::PhantomData<T>);

impl<T: Integer + Unsigned + Copy + Hash> MinDNF<T> {
    pub fn min_dnf(nnf: NNFFormula<T>) -> NNFFormula<T> {
        match nnf {
            NNFFormula::True | NNFFormula::False | NNFFormula::AP(..) => nnf,
            NNFFormula::Until(lhs, int, rhs) => {
                NNFFormula::until(Self::min_dnf(*lhs), int, Self::min_dnf(*rhs))
            }
            NNFFormula::Release(lhs, int, rhs) => {
                NNFFormula::release(Self::min_dnf(*lhs), int, Self::min_dnf(*rhs))
            }
            _ => {
                let clauses = Self::min_clause_set(nnf);
                // Also all temporal "literals" in the DNF should be in minimal DNF
                let clauses_with_minimal_literals = clauses
                    .into_iter()
                    .map(|clause| clause.into_iter().map(Self::min_dnf).collect_vec());
                NNFFormula::or(clauses_with_minimal_literals.map(NNFFormula::and))
            }
        }
    }

    pub fn min_clause_set(nnf: NNFFormula<T>) -> ClauseSet<NNFFormula<T>> {
        let mut dnf = match nnf {
            NNFFormula::True => Self::make_true_clause_set(),
            NNFFormula::False => Self::make_false_clause_set(),
            NNFFormula::AP(..) | NNFFormula::Until(..) | NNFFormula::Release(..) => {
                Self::make_literal_clause_set(nnf)
            }
            NNFFormula::And(subs) => subs
                .into_iter()
                .map(Self::min_clause_set)
                .reduce(min_product)
                .unwrap_or_else(Self::make_true_clause_set),
            NNFFormula::Or(subs) => subs
                .into_iter()
                .map(Self::min_clause_set)
                .reduce(min_union)
                .unwrap_or_else(Self::make_false_clause_set),
        };
        Self::remove_contradictions(&mut dnf);
        dnf
    }

    fn make_true_clause_set<F: Ord + Hash>() -> ClauseSet<F> {
        ClauseSet::from([Clause::new()])
    }

    fn make_false_clause_set<F>() -> ClauseSet<F> {
        ClauseSet::new()
    }

    fn make_literal_clause_set<F: Ord + Hash>(literal: F) -> ClauseSet<F> {
        ClauseSet::from([Clause::from([literal])])
    }

    fn remove_contradictions(dnf: &mut ClauseSet<NNFFormula<T>>) {
        dnf.retain(|clause| !Self::is_contradiction(clause))
    }

    fn is_contradiction(clause: &Clause<NNFFormula<T>>) -> bool {
        clause
            .iter()
            .any(|literal| clause.iter().any(|other| other.is_negation_of(literal)))
    }
}

fn min_product<F: Clone + Hash + Ord>(a: ClauseSet<F>, b: ClauseSet<F>) -> ClauseSet<F> {
    let mut a_by_size: BTreeMap<usize, ClauseSet<F>> = BTreeMap::new();
    a.into_iter().for_each(|clause| {
        a_by_size.entry(clause.len()).or_default().insert(clause);
    });
    let mut b_by_size: BTreeMap<usize, ClauseSet<F>> = BTreeMap::new();
    b.into_iter().for_each(|clause| {
        b_by_size.entry(clause.len()).or_default().insert(clause);
    });

    let mut results = ClauseSet::new();

    // We want to process the smallest clauses first, as this improves our chances of excluding larger clauses later on
    let sizes = iproduct!(a_by_size.keys().copied(), b_by_size.keys().copied())
        .sorted_unstable_by_key(|(a, b)| a + b); // a + b overestimates the size of the union
    for (size_a, size_b) in sizes {
        let mut new_results = ClauseSet::new();

        let clauses_a = a_by_size.get(&size_a).expect("size_a is from the key set");
        let clauses_b = b_by_size.get(&size_b).expect("size_b is from the key set");
        for (clause_a, clause_b) in iproduct!(clauses_a, clauses_b) {
            let union = clause_a.union(clause_b).cloned().collect();
            // If there is not already a smaller clause in the results, remove all supersets and add the union
            if !any_is_subset(&union, &results) && !any_is_subset(&union, &new_results) {
                remove_supersets(&union, &mut results);
                remove_supersets(&union, &mut new_results);
                new_results.insert(union);
            }
        }

        // In the future we can skip all sets that are supersets of one of our new results
        for clause in &new_results {
            for map in [&mut a_by_size, &mut b_by_size] {
                map.range_mut(clause.len()..).for_each(|(_, clause_set)| {
                    remove_supersets(clause, clause_set);
                });
            }
        }

        results.extend(new_results);
    }

    results
}

fn min_union<F: Ord + Hash>(a: ClauseSet<F>, b: ClauseSet<F>) -> ClauseSet<F> {
    let mut a = a
        .into_iter()
        .sorted_unstable_by_key(|clause| clause.len())
        .peekable();
    let mut b = b
        .into_iter()
        .sorted_unstable_by_key(|clause| clause.len())
        .peekable();

    let mut from_a = ClauseSet::new();
    let mut from_b = ClauseSet::new();
    let mut current_size = 0;
    while a.peek().is_some() || b.peek().is_some() {
        add_all_of_size_if_no_smaller_exists(current_size, &mut a, &from_b, &mut from_a);
        add_all_of_size_if_no_smaller_exists(current_size, &mut b, &from_a, &mut from_b);

        current_size += 1;
    }
    from_a.extend(from_b);
    from_a
}

fn add_all_of_size_if_no_smaller_exists<F: Ord + Hash>(
    size: usize,
    to_add: &mut Peekable<impl Iterator<Item = Clause<F>>>,
    existing: &ClauseSet<F>,
    out: &mut ClauseSet<F>,
) {
    while let Some(v) = to_add.peek() {
        if v.len() > size {
            break;
        }
        let v = to_add.next().expect("Peeked value is not None");
        if !any_is_subset(&v, existing) {
            out.insert(v);
        }
    }
}

fn remove_supersets<F: Ord>(subset: &Clause<F>, sets: &mut ClauseSet<F>) {
    sets.retain(|set| !subset.is_subset(set));
}

fn any_is_subset<'a, F: Ord + 'a>(
    a: &Clause<F>,
    bs: impl IntoIterator<Item = &'a Clause<F>>,
) -> bool {
    bs.into_iter().any(|b| b.is_subset(a))
}

#[cfg(test)]
mod test {
    use crate::parser::mltl_parser;

    use super::*;

    #[test]
    fn test_min_dnf() {
        let phi = mltl_parser::formula("a | (a & F[1, 1] b) | (F[0, 10] (b | c))")
            .expect("Syntax is correct");
        let dnf = mltl_parser::formula("a | (F[0, 10] (b | c))").expect("Syntax is correct");
        assert_eq!(MinDNF::min_dnf(phi.into()), dnf.into());
    }

    #[test]
    fn test_min_dnf2() {
        let phi = mltl_parser::formula("(a -> b) & a").expect("Syntax is correct");
        let dnf = mltl_parser::formula("a & b").expect("Syntax is correct");
        assert_eq!(MinDNF::min_dnf(phi.into()), dnf.into());
    }

    #[test]
    fn test_min_union() {
        let a = ClauseSet::from([Clause::from([1]), Clause::from([1, 2, 3])]);
        let b = ClauseSet::from([Clause::from([2, 3]), Clause::from([1, 2])]);
        let c = ClauseSet::from([Clause::from([1]), Clause::from([2, 3])]);
        assert_eq!(min_union(a, b), c);
    }

    #[test]
    fn test_min_product() {
        let a = ClauseSet::from([Clause::from([1]), Clause::from([1, 2, 3])]);
        let b = ClauseSet::from([Clause::from([2, 3]), Clause::from([1, 2])]);
        let c = ClauseSet::from([Clause::from([1, 2])]);
        assert_eq!(min_product(a, b), c);
    }
}
