use std::hash::Hash;

use multimap::MultiMap;
use num::{Integer, Unsigned};

use crate::{formula::NNFFormula, minimal_dnf::MinDNF, sets::interval::Interval};

pub struct Rewriter<T>(std::marker::PhantomData<T>);

type UntilReleaseRestVectors<T> = (Vec<NNFFormula<T>>, Vec<NNFFormula<T>>, Vec<NNFFormula<T>>);
type KeyIntervalFormulas<T> = (NNFFormula<T>, Interval<T>, Vec<NNFFormula<T>>);

impl<T: Integer + Unsigned + Copy + Hash> Rewriter<T> {
    pub fn rewrite(nnf: NNFFormula<T>) -> NNFFormula<T> {
        MinDNF::min_dnf(Self::combine_temporal(nnf))
    }

    pub fn combine_temporal(nnf: NNFFormula<T>) -> NNFFormula<T> {
        match nnf {
            NNFFormula::And(subs) => {
                // Rewrite all subformulas
                let subs = subs.into_iter().map(Self::combine_temporal);
                // Extract untils and releases
                let (untils, releases, mut rest) = Self::extract_until_and_release(subs);

                // Apply \phi U \gamma & \psi U \gamma = (\phi & \psi) U \gamma (adapted for intervals)
                let new_untils =
                    Self::grouped_interval_merge(untils.into_iter().map(|f| match f {
                        // We use the rhs as the key to group the untils
                        NNFFormula::Until(lhs, int, key) => (*key, int, *lhs),
                        _ => unreachable!(),
                    }))
                    .into_iter()
                    .map(|(key, int, lhs)| NNFFormula::until(NNFFormula::and(lhs), int, key));

                // Apply \gamma R \phi & \gamma R \psi = \gamma R (\phi & \psi) (adapted for intervals)
                let new_releases =
                    Self::grouped_interval_merge(releases.into_iter().map(|f| match f {
                        // We use the lhs as the key to group the releases
                        NNFFormula::Release(key, int, rhs) => (*key, int, *rhs),
                        _ => unreachable!(),
                    }))
                    .into_iter()
                    .map(|(key, int, rhs)| NNFFormula::release(key, int, NNFFormula::and(rhs)));

                rest.extend(new_untils);
                rest.extend(new_releases);
                NNFFormula::and(rest)
            }
            NNFFormula::Or(subs) => {
                // Rewrite all subformulas
                let subs = subs.into_iter().map(Self::combine_temporal);
                // Extract untils and releases
                let (untils, releases, mut rest) = Self::extract_until_and_release(subs);

                // Apply \gamma U \phi | \gamma U \psi = \gamma U (\phi | \psi) (adapted for intervals)
                let new_untils =
                    Self::grouped_interval_merge(untils.into_iter().map(|f| match f {
                        // We use the lhs as the key to group the untils
                        NNFFormula::Until(key, int, rhs) => (*key, int, *rhs),
                        _ => unreachable!(),
                    }))
                    .into_iter()
                    .map(|(key, int, rhs)| NNFFormula::until(key, int, NNFFormula::or(rhs)));

                // Apply \phi R \gamma | \psi R \gamma = (\phi | \psi) R \gamma (adapted for intervals)
                let new_releases =
                    Self::grouped_interval_merge(releases.into_iter().map(|f| match f {
                        // We use the rhs as the key to group the releases
                        NNFFormula::Release(lhs, int, key) => (*key, int, *lhs),
                        _ => unreachable!(),
                    }))
                    .into_iter()
                    .map(|(key, int, lhs)| NNFFormula::release(NNFFormula::or(lhs), int, key));

                rest.extend(new_untils);
                rest.extend(new_releases);
                NNFFormula::or(rest)
            }
            NNFFormula::Until(lhs, int, rhs) => NNFFormula::until(
                Self::combine_temporal(*lhs),
                int,
                Self::combine_temporal(*rhs),
            ),
            NNFFormula::Release(lhs, int, rhs) => NNFFormula::release(
                Self::combine_temporal(*lhs),
                int,
                Self::combine_temporal(*rhs),
            ),
            _ => nnf,
        }
    }

    fn extract_until_and_release(
        nnfs: impl Iterator<Item = NNFFormula<T>>,
    ) -> UntilReleaseRestVectors<T> {
        let (untils, rest): (Vec<_>, Vec<_>) =
            nnfs.partition(|f| matches!(f, NNFFormula::Until(..)));
        let (releases, rest): (Vec<_>, Vec<_>) = rest
            .into_iter()
            .partition(|f| matches!(f, NNFFormula::Release(..)));
        (untils, releases, rest)
    }

    fn grouped_interval_merge(
        formulas: impl Iterator<Item = (NNFFormula<T>, Interval<T>, NNFFormula<T>)>,
    ) -> Vec<KeyIntervalFormulas<T>> {
        let multi_map: MultiMap<_, _> = formulas.map(|(key, int, val)| (key, (int, val))).collect();
        multi_map
            .iter_all()
            .flat_map(|(key, intervals)| {
                Interval::merge(intervals.clone())
                    .into_iter()
                    .map(move |(int, vals)| ((*key).clone(), int, vals))
            })
            .collect()
    }
}

#[cfg(test)]
mod test {
    use crate::parser::mltl_parser;

    use super::*;

    #[test]
    fn test_rewrite() {
        let phi =
            mltl_parser::formula("(a U[1, 4] c) & (b U[3, 10] c)").expect("Syntax is correct");

        let expected = mltl_parser::formula("(a U[1, 2] c) & (a & b U[3, 4] c) & (b U[5, 10] c)")
            .expect("Syntax is correct");
        let rewritten = Rewriter::rewrite(phi.into());

        assert_eq!(rewritten, expected.into(),)
    }

    #[test]
    fn test_rewrite2() {
        let phi =
            mltl_parser::formula("(G[0, 10] a -> b) & G[0, 11] a").expect("Syntax is correct");

        let expected =
            mltl_parser::formula("(G[0, 10] b & a) & G[11, 11] a").expect("Syntax is correct");
        let rewritten = Rewriter::rewrite(phi.into());

        assert_eq!(rewritten, expected.into())
    }
}
