use std::iter::Peekable;

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

fn min_product<T>(mut a: Vec<Vec<T>>, mut b: Vec<Vec<T>>) -> Vec<Vec<T>> {
    a.sort_unstable_by_key(|v| v.len());
    b.sort_unstable_by_key(|v| v.len());
    todo!()
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
        let v = to_add.next().unwrap();
        if !existing.iter().any(|b| contains_all(&v, b)) {
            out.push(v);
        }
    }
}

fn contains_all<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    b.iter().all(|x| a.contains(x))
}

#[cfg(test)]
mod test {
    #[test]
    fn test_min_union() {
        let a = vec![vec![1], vec![1, 2, 3]];
        let b = vec![vec![1, 2], vec![2, 3]];
        let c = vec![vec![1], vec![2, 3]];
        assert_eq!(super::min_union(a, b), c);
    }
}
