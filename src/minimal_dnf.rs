use std::{
    collections::{BTreeSet, HashSet},
    iter::Peekable,
};

use itertools::{iproduct, Itertools};
use multimap::MultiMap;

use crate::formula::NNFFormula;

type Clause<T> = BTreeSet<T>;
type ClauseSet<T> = BTreeSet<Clause<T>>;

pub fn min_dnf(nnf: NNFFormula) -> NNFFormula {
    match nnf {
        NNFFormula::True | NNFFormula::False | NNFFormula::AP(..) => nnf,
        NNFFormula::Until(lhs, int, rhs) => NNFFormula::until(min_dnf(*lhs), int, min_dnf(*rhs)),
        NNFFormula::Release(lhs, int, rhs) => {
            NNFFormula::release(min_dnf(*lhs), int, min_dnf(*rhs))
        }
        _ => {
            let clauses = min_clause_set(nnf);
            // Also all temporal "literals" in the DNF should be in minimal DNF
            let clauses_with_minimal_literals = clauses
                .into_iter()
                .map(|clause| clause.into_iter().map(min_dnf).collect_vec());
            NNFFormula::or(clauses_with_minimal_literals.map(NNFFormula::and))
        }
    }
}

pub fn min_clause_set(nnf: NNFFormula) -> ClauseSet<NNFFormula> {
    let mut dnf = match nnf {
        NNFFormula::True => make_true_clause_set(),
        NNFFormula::False => make_false_clause_set(),
        NNFFormula::AP(..) | NNFFormula::Until(..) | NNFFormula::Release(..) => {
            make_literal_clause_set(nnf)
        }
        NNFFormula::And(subs) => subs
            .into_iter()
            .map(min_clause_set)
            .reduce(min_product)
            .unwrap_or_else(make_true_clause_set),
        NNFFormula::Or(subs) => subs
            .into_iter()
            .map(min_clause_set)
            .reduce(min_union)
            .unwrap_or_else(make_false_clause_set),
    };
    remove_contradictions(&mut dnf);
    dnf
}

fn make_true_clause_set<T: Ord>() -> ClauseSet<T> {
    BTreeSet::from([BTreeSet::new()])
}

fn make_false_clause_set<T>() -> ClauseSet<T> {
    BTreeSet::new()
}

fn make_literal_clause_set<T: Ord>(literal: T) -> ClauseSet<T> {
    BTreeSet::from([BTreeSet::from([literal])])
}

fn remove_contradictions(dnf: &mut ClauseSet<NNFFormula>) {
    dnf.retain(|clause| !is_contradiction(clause))
}

fn is_contradiction(clause: &Clause<NNFFormula>) -> bool {
    clause
        .iter()
        .any(|literal| clause.contains(&literal.clone().not()))
}

fn min_product<T: Clone + Eq + std::hash::Hash + Ord>(
    a: ClauseSet<T>,
    b: ClauseSet<T>,
) -> ClauseSet<T> {
    let mut a_by_size: MultiMap<_, Clause<T>> = a.into_iter().map(|v| (v.len(), v)).collect();
    let mut b_by_size: MultiMap<_, Clause<T>> = b.into_iter().map(|v| (v.len(), v)).collect();

    let sizes: HashSet<_> = iproduct!(a_by_size.keys().copied(), b_by_size.keys().copied())
        .sorted_unstable_by_key(|(a, b)| a + b)
        .collect();

    let mut result: ClauseSet<T> = BTreeSet::new();
    for (size_a, size_b) in sizes {
        let vec_a = a_by_size
            .get_vec(&size_a)
            .expect("size_a is from the key set");
        let vec_b = b_by_size
            .get_vec(&size_b)
            .expect("size_b is from the key set");

        let mut new_results: ClauseSet<T> = BTreeSet::new();
        for (a, b) in iproduct!(vec_a, vec_b) {
            let union = a.iter().chain(b.iter()).unique().cloned().collect();
            if !any_fully_contained(&union, result.iter())
                && !any_fully_contained(&union, new_results.iter())
            {
                remove_supersets(&union, &mut result);
                remove_supersets(&union, &mut new_results);
                new_results.insert(union);
            }
        }

        // In the future we can skip all sets that are supersets of one of our results
        for (size, vec) in a_by_size.iter_all_mut() {
            if size > &size_a {
                new_results.iter().for_each(|new| {
                    remove_supersets_vec(new, vec);
                });
            }
        }
        for (size, vec) in b_by_size.iter_all_mut() {
            if size > &size_b {
                new_results.iter().for_each(|new| {
                    remove_supersets_vec(new, vec);
                });
            }
        }

        result.append(&mut new_results);
    }

    result
}

fn min_union<T: Ord>(a: ClauseSet<T>, b: ClauseSet<T>) -> ClauseSet<T> {
    let mut a = a
        .into_iter()
        .sorted_unstable_by_key(|clause| clause.len())
        .peekable();
    let mut b = b
        .into_iter()
        .sorted_unstable_by_key(|clause| clause.len())
        .peekable();

    let mut from_a: ClauseSet<T> = BTreeSet::new();
    let mut from_b: ClauseSet<T> = BTreeSet::new();
    let mut current_size = 0;
    while a.peek().is_some() || b.peek().is_some() {
        add_all_of_size_if_no_smaller_exists(current_size, &mut a, &from_b, &mut from_a);
        add_all_of_size_if_no_smaller_exists(current_size, &mut b, &from_a, &mut from_b);

        current_size += 1;
    }
    from_a.extend(from_b);
    from_a
}

fn add_all_of_size_if_no_smaller_exists<T: Ord>(
    size: usize,
    to_add: &mut Peekable<impl Iterator<Item = Clause<T>>>,
    existing: &ClauseSet<T>,
    out: &mut ClauseSet<T>,
) {
    while let Some(v) = to_add.peek() {
        if v.len() > size {
            break;
        }
        let v = to_add.next().expect("Peeked value is not None");
        if !existing.iter().any(|b| contains_all(&v, b)) {
            out.insert(v);
        }
    }
}

fn remove_supersets<T: Ord>(subset: &Clause<T>, sets: &mut ClauseSet<T>) {
    sets.retain(|set| !contains_all(set, subset));
}

fn remove_supersets_vec<T: Ord>(subset: &Clause<T>, sets: &mut Vec<Clause<T>>) {
    sets.retain(|set| !contains_all(set, subset));
}

fn any_fully_contained<'a, T: Ord + 'a>(
    a: &Clause<T>,
    mut bs: impl Iterator<Item = &'a Clause<T>>,
) -> bool {
    bs.any(|b| contains_all(a, b))
}

fn contains_all<T: Ord>(a: &Clause<T>, b: &Clause<T>) -> bool {
    b.iter().all(|x| a.contains(x))
}

#[cfg(test)]
mod test {
    use crate::{formula::Formula, interval::Interval};

    use super::*;

    #[test]
    fn test_min_dnf() {
        let a = NNFFormula::AP("a".to_string(), false);
        let b = NNFFormula::AP("b".to_string(), false);
        let c = NNFFormula::AP("c".to_string(), false);
        let phi = NNFFormula::or([
            a.clone(),
            NNFFormula::and([
                a.clone(),
                NNFFormula::until(NNFFormula::True, Interval::from_endpoints(1, 1), b.clone()),
            ]),
            NNFFormula::until(
                NNFFormula::True,
                Interval::from_endpoints(0, 10),
                NNFFormula::or([b.clone(), c.clone()]),
            ),
        ]);

        let dnf = NNFFormula::or([
            a,
            NNFFormula::until(
                NNFFormula::True,
                Interval::from_endpoints(0, 10),
                NNFFormula::or([b, c]),
            ),
        ]);

        assert_eq!(min_dnf(phi), dnf);
    }

    #[test]
    fn test_min_dnf2() {
        let a = Formula::AP("a".to_string());
        let b = Formula::AP("b".to_string());

        let phi = Formula::and([Formula::implies(a.clone(), b), a.clone()]);

        let dnf = NNFFormula::and([
            NNFFormula::AP("a".to_string(), false),
            NNFFormula::AP("b".to_string(), false),
        ]);
        assert_eq!(min_dnf(phi.into()), dnf);
    }

    #[test]
    fn test_min_union() {
        let a = BTreeSet::from([BTreeSet::from([1]), BTreeSet::from([1, 2, 3])]);
        let b = BTreeSet::from([BTreeSet::from([2, 3]), BTreeSet::from([1, 2])]);
        let c = BTreeSet::from([BTreeSet::from([1]), BTreeSet::from([2, 3])]);
        assert_eq!(super::min_union(a, b), c);
    }

    #[test]
    fn test_min_product() {
        let a = BTreeSet::from([BTreeSet::from([1]), BTreeSet::from([1, 2, 3])]);
        let b = BTreeSet::from([BTreeSet::from([2, 3]), BTreeSet::from([1, 2])]);
        let c = BTreeSet::from([BTreeSet::from([1, 2])]);
        assert_eq!(super::min_product(a, b), c);
    }
}
