use multimap::MultiMap;

use crate::{formula::NNFFormula, interval::Interval, minimal_dnf::min_dnf};

pub fn combine_temporal(nnf: NNFFormula) -> NNFFormula {
    match nnf {
        NNFFormula::And(subs) => {
            // Rewrite all subformulas
            let subs = subs.into_iter().map(combine_temporal);
            // Extract untils and releases
            let (untils, releases, mut rest) = extract_until_and_release(subs);

            // Apply \phi U \gamma & \psi U \gamma = (\phi & \psi) U \gamma (adapted for intervals)
            let new_untils = grouped_interval_merge(untils.into_iter().map(|f| match f {
                // We use the rhs as the key to group the untils
                NNFFormula::Until(lhs, int, key) => (*key, int, *lhs),
                _ => unreachable!(),
            }))
            .into_iter()
            .map(|(key, int, lhs)| NNFFormula::until(NNFFormula::and(lhs), int, key));

            // Apply \gamma R \phi & \gamma R \psi = \gamma R (\phi & \psi) (adapted for intervals)
            let new_releases = grouped_interval_merge(releases.into_iter().map(|f| match f {
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
            let subs = subs.into_iter().map(combine_temporal);
            // Extract untils and releases
            let (untils, releases, mut rest) = extract_until_and_release(subs);

            // Apply \gamma U \phi | \gamma U \psi = \gamma U (\phi | \psi) (adapted for intervals)
            let new_untils = grouped_interval_merge(untils.into_iter().map(|f| match f {
                // We use the lhs as the key to group the untils
                NNFFormula::Until(key, int, rhs) => (*key, int, *rhs),
                _ => unreachable!(),
            }))
            .into_iter()
            .map(|(key, int, rhs)| NNFFormula::until(key, int, NNFFormula::or(rhs)));

            // Apply \phi R \gamma | \psi R \gamma = (\phi | \psi) R \gamma (adapted for intervals)
            let new_releases = grouped_interval_merge(releases.into_iter().map(|f| match f {
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
        NNFFormula::Until(lhs, int, rhs) => {
            NNFFormula::until(combine_temporal(*lhs), int, combine_temporal(*rhs))
        }
        NNFFormula::Release(lhs, int, rhs) => {
            NNFFormula::release(combine_temporal(*lhs), int, combine_temporal(*rhs))
        }
        _ => nnf,
    }
}

fn extract_until_and_release(
    nnfs: impl Iterator<Item = NNFFormula>,
) -> (Vec<NNFFormula>, Vec<NNFFormula>, Vec<NNFFormula>) {
    let (untils, rest): (Vec<_>, Vec<_>) = nnfs.partition(|f| matches!(f, NNFFormula::Until(..)));
    let (releases, rest): (Vec<_>, Vec<_>) = rest
        .into_iter()
        .partition(|f| matches!(f, NNFFormula::Release(..)));
    (untils, releases, rest)
}

fn grouped_interval_merge(
    formulas: impl Iterator<Item = (NNFFormula, Interval, NNFFormula)>,
) -> Vec<(NNFFormula, Interval, Vec<NNFFormula>)> {
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

#[cfg(test)]
mod test {
    use crate::formula::Formula;

    use super::*;

    #[test]
    fn test_rewrite() {
        let phi = NNFFormula::And(vec![
            NNFFormula::until(
                NNFFormula::AP("a".to_string(), true),
                Interval::from_endpoints(1, 4),
                NNFFormula::AP("c".to_string(), true),
            ),
            NNFFormula::until(
                NNFFormula::AP("b".to_string(), true),
                Interval::from_endpoints(3, 10),
                NNFFormula::AP("c".to_string(), true),
            ),
        ]);

        let rewritten = min_dnf(combine_temporal(phi));

        assert_eq!(
            rewritten,
            NNFFormula::And(vec![
                NNFFormula::until(
                    NNFFormula::AP("a".to_string(), true),
                    Interval::from_endpoints(1, 2),
                    NNFFormula::AP("c".to_string(), true),
                ),
                NNFFormula::until(
                    NNFFormula::And(vec![
                        NNFFormula::AP("a".to_string(), true),
                        NNFFormula::AP("b".to_string(), true),
                    ]),
                    Interval::from_endpoints(3, 4),
                    NNFFormula::AP("c".to_string(), true),
                ),
                NNFFormula::until(
                    NNFFormula::AP("b".to_string(), true),
                    Interval::from_endpoints(5, 10),
                    NNFFormula::AP("c".to_string(), true),
                ),
            ])
        )
    }

    #[test]
    fn test_rewrite2() {
        let phi = Formula::and(vec![
            Formula::globally(
                Interval::from_endpoints(0, 10),
                Formula::implies(Formula::AP("a".to_string()), Formula::AP("b".to_string())),
            ),
            Formula::globally(
                Interval::from_endpoints(0, 11),
                Formula::AP("a".to_string()),
            ),
        ]);

        let nnf = NNFFormula::from(phi);
        dbg!(&nnf);

        let combined = combine_temporal(nnf);
        dbg!(&combined);

        let rewritten = min_dnf(combined);
        dbg!(&rewritten);
    }
}
