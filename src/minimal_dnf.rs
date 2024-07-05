use std::{collections::HashSet, iter::Peekable};

use itertools::Itertools;
use multimap::MultiMap;

use crate::formula::NNFFormula;

pub fn f(nnf: NNFFormula) -> Vec<Vec<NNFFormula>> {
    match nnf {
        NNFFormula::True => vec![vec![]],
        NNFFormula::False => vec![],
        NNFFormula::AP(..) | NNFFormula::Until(..) | NNFFormula::Release(..) => vec![vec![nnf]],
        NNFFormula::And(subs) => subs.into_iter().map(f).reduce(min_product).unwrap(),
        NNFFormula::Or(subs) => subs.into_iter().map(f).reduce(min_union).unwrap(),
    }
}

fn min_product<T: Clone + Eq + std::hash::Hash>(a: Vec<Vec<T>>, b: Vec<Vec<T>>) -> Vec<Vec<T>> {
    let mut a_by_size: MultiMap<_, Vec<T>> = a.into_iter().map(|v| (v.len(), v)).collect();
    let mut b_by_size: MultiMap<_, Vec<T>> = b.into_iter().map(|v| (v.len(), v)).collect();

    let sizes: HashSet<_> = iproduct!(a_by_size.keys().copied(), b_by_size.keys().copied())
        .sorted_unstable_by_key(|(a, b)| a + b)
        .collect();

    let mut result: Vec<Vec<_>> = Vec::new();
    for (size_a, size_b) in sizes {
        let vec_a = a_by_size
            .get_vec(&size_a)
            .expect("size_a is from the key set");
        let vec_b = b_by_size
            .get_vec(&size_b)
            .expect("size_b is from the key set");

        let mut new_results: Vec<Vec<_>> = Vec::new();
        for (a, b) in iproduct!(vec_a, vec_b) {
                let union: Vec<_> = a.iter().chain(b.iter()).unique().cloned().collect();
                if !any_fully_contained(&union, result.iter())
                    && !any_fully_contained(&union, new_results.iter())
                {
                    remove_supersets(&union, &mut result);
                    remove_supersets(&union, &mut new_results);
                    new_results.push(union);
            }
        }

        // In the future we can skip all sets that are supersets of one of our results
        for (size, vec) in a_by_size.iter_all_mut() {
            if size > &size_a {
                new_results.iter().for_each(|new| {
                    remove_supersets(&new, vec);
                });
            }
        }
        for (size, vec) in b_by_size.iter_all_mut() {
            if size > &size_b {
                new_results.iter().for_each(|new| {
                    remove_supersets(&new, vec);
                });
            }
        }

        result.extend(new_results);
    }

    result
}

fn min_union<T: Ord>(mut a: Vec<Vec<T>>, mut b: Vec<Vec<T>>) -> Vec<Vec<T>> {
    a.sort_unstable_by_key(|v| v.len());
    b.sort_unstable_by_key(|v| v.len());
    let mut a = a.into_iter().peekable();
    let mut b = b.into_iter().peekable();

    let mut from_a: Vec<Vec<T>> = Vec::new();
    let mut from_b: Vec<Vec<T>> = Vec::new();
    let mut current_size = 0;
    while a.peek().is_some() || b.peek().is_some() {
        add_all_of_size_if_no_smaller_exists(current_size, &mut a, &from_b, &mut from_a);
        add_all_of_size_if_no_smaller_exists(current_size, &mut b, &from_a, &mut from_b);

        current_size += 1;
    }
    from_a.extend(from_b);
    from_a
}

fn add_all_of_size_if_no_smaller_exists<T: Eq>(
    size: usize,
    to_add: &mut Peekable<impl Iterator<Item = Vec<T>>>,
    existing: &Vec<Vec<T>>,
    out: &mut Vec<Vec<T>>,
) {
    while let Some(v) = to_add.peek() {
        if v.len() > size {
            break;
        }
        let v = to_add.next().expect("Peeked value is not None");
        if !existing.iter().any(|b| contains_all(&v, b)) {
            out.push(v);
        }
    }
}

fn remove_supersets<T: PartialEq>(subset: &Vec<T>, sets: &mut Vec<Vec<T>>) {
    sets.retain(|set| !contains_all(set, &subset));
}

fn any_fully_contained<'a, T: PartialEq + 'a>(
    a: &[T],
    mut bs: impl Iterator<Item = &'a Vec<T>>,
) -> bool {
    bs.any(|b| contains_all(a, &b))
}

fn contains_all<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    b.iter().all(|x| a.contains(x))
}

#[cfg(test)]
mod test {
    #[test]
    fn test_min_union() {
        let a = vec![vec![1], vec![1, 2, 3]];
        let b = vec![vec![2, 3], vec![1, 2]];
        let c = vec![vec![1], vec![2, 3]];
        assert_eq!(super::min_union(a, b), c);
    }

    #[test]
    fn test_min_product() {
        let a = vec![vec![1], vec![1, 2, 3]];
        let b = vec![vec![2, 3], vec![1, 2]];
        let c = vec![vec![1, 2]];
        assert_eq!(super::min_product(a, b), c);
    }
}
