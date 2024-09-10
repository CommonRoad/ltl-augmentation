use std::hash::Hash;

use itertools::iproduct;
use num::{traits::SaturatingSub, Integer, Unsigned};

use crate::{
    formula::{AtomicProposition, NNFFormula},
    sets::interval_set::IntervalSet,
};

use super::predicates as pred;

#[derive(Debug, Clone, Copy)]
pub struct Implication {
    pub key: &'static str,
    pub pre: &'static str,
    pub pre_neg: bool,
    pub post: &'static str,
    pub post_neg: bool,
}

pub const ALL: [Implication; 2] = [SAFE_DISTANCE, IN_FRONT_OF];

pub const SAFE_DISTANCE: Implication = Implication {
    key: "safe_distance_impl",
    pre: pred::KEEPS_SAFE_DISTANCE_PREC,
    pre_neg: false,
    post: pred::KEEPS_SAFE_DISTANCE_PREC,
    post_neg: false,
};

pub const IN_FRONT_OF: Implication = Implication {
    key: "in_front_of_impl",
    pre: pred::IN_FRONT_OF,
    pre_neg: false,
    post: pred::IN_FRONT_OF,
    post_neg: false,
};

// TODO: Add more implications

pub fn find_necessary_implications<T>(
    formula: &NNFFormula<T>,
) -> Vec<(AtomicProposition, AtomicProposition, IntervalSet<T>)>
where
    T: Integer + Unsigned + Copy + SaturatingSub + Hash,
{
    let aps_over_time = formula.collect_aps_with_time();
    ALL.iter()
        .flat_map(|imp| {
            let potential_preconditions = aps_over_time
                .iter()
                .filter(|(ap, _)| ap.name.starts_with(imp.pre) && ap.negated == imp.pre_neg);
            let potential_postconditions = aps_over_time
                .iter()
                .filter(|(ap, _)| ap.name.starts_with(imp.post) && ap.negated == imp.post_neg);
            iproduct!(potential_preconditions, potential_postconditions)
                .filter(|(pre, post)| pre != post)
                .map(|(pre, post)| (pre.0.clone(), post.0.clone(), pre.1.intersect(post.1)))
                .filter(|(.., intervals)| !intervals.is_empty())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{parser::mltl_parser, sets::interval::Interval};

    use super::*;

    #[test]
    fn test_find_necessary_implications() {
        let formula = mltl_parser::formula(
            format!(
                "(G[0, 5] {}_V42 & {}_V42) | (G[2, 7] {}_V3 & ! {}_V3) | (G[10, 20] {}_V3)",
                SAFE_DISTANCE.pre,
                IN_FRONT_OF.pre,
                SAFE_DISTANCE.post,
                IN_FRONT_OF.post,
                IN_FRONT_OF.post
            )
            .as_str(),
        )
        .expect("Syntax is correct")
        .into();
        let implications = find_necessary_implications(&formula);
        assert_eq!(
            implications,
            vec![
                (
                    AtomicProposition {
                        name: Rc::from(format!("{}_V42", SAFE_DISTANCE.pre)),
                        negated: false
                    },
                    AtomicProposition {
                        name: Rc::from(format!("{}_V3", SAFE_DISTANCE.post)),
                        negated: false
                    },
                    Interval::bounded(2, 5).into()
                ),
                (
                    AtomicProposition {
                        name: Rc::from(format!("{}_V3", SAFE_DISTANCE.post)),
                        negated: false
                    },
                    AtomicProposition {
                        name: Rc::from(format!("{}_V42", SAFE_DISTANCE.pre)),
                        negated: false
                    },
                    Interval::bounded(2, 5).into()
                ),
            ]
        );
    }
}
