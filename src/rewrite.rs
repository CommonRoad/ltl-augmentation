use multimap::MultiMap;

use crate::{formula::NNFFormula, interval::Interval};

pub fn rewrite(nnf: NNFFormula) -> NNFFormula {
    match nnf {
        NNFFormula::And(subs) => {
            let untils: MultiMap<_, _> = subs
                .iter()
                .filter_map(|f| match f {
                    NNFFormula::Until(lhs, int, rhs) => Some((rhs, (*int, lhs))),
                    _ => None,
                })
                .collect();
            let new_subs = untils
                .iter_all()
                .flat_map(|(rhs, intervals)| {
                    Interval::merge(intervals.clone())
                        .into_iter()
                        .map(|(int, lhs)| {
                            NNFFormula::Until(
                                Box::new(NNFFormula::And(
                                    lhs.into_iter().map(|f| (**f).clone()).collect(),
                                )),
                                int,
                                (*rhs).clone(),
                            )
                        })
                })
                .collect();

            NNFFormula::And(new_subs)
        }
        _ => nnf,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_rewrite() {
        let phi = NNFFormula::And(vec![
            NNFFormula::Until(
                Box::new(NNFFormula::AP("a".to_string(), true)),
                Interval::from_endpoints(1, 4),
                Box::new(NNFFormula::AP("c".to_string(), true)),
            ),
            NNFFormula::Until(
                Box::new(NNFFormula::AP("b".to_string(), true)),
                Interval::from_endpoints(3, 10),
                Box::new(NNFFormula::AP("c".to_string(), true)),
            ),
        ]);

        let phi = rewrite(phi);

        dbg!(phi);
    }
}
