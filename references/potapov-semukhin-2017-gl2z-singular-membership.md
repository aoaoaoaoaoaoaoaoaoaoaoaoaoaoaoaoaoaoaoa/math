# Potapov and Semukhin (2017)

**Citation.** Igor Potapov and Pavel Semukhin, “Membership Problem in `GL(2,ℤ)`
Extended by Singular Matrices,” in *MFCS 2017*, LIPIcs **83**, Article 44,
44:1–44:13, 2017.

- DOI: https://doi.org/10.4230/LIPIcs.MFCS.2017.44
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2017.44
- Local PDF: `potapov-semukhin-2017-gl2z-singular-membership.pdf`
- Retrieved: 2026-07-21
- SHA-256: `00637478dec1ac3d382ad4e93687510f8ca599553a6c509ebb4f09d857a3c4ce`

## Results used

Theorem 8 decides membership for a semigroup of `2 × 2` integer matrices when every
generator is either singular or belongs to `GL(2,ℤ)`. Theorem 11 specializes this to
mortality: mortality is decidable for arbitrary finite integer families whose determinants
belong to `{0, 1, −1}`. The proof combines Smith normal form with effective intersection
of regular subsets of `GL(2,ℤ)`.

For the dimension-two campaign this excludes the whole unimodular stratum. Any genuinely
unresolved family must contain at least one nonsingular generator of absolute determinant
greater than one; combined with Heckman's result, the difficult core contains at least two
nonsingular generators.

## Audit notes

This is a peer-reviewed, CC-BY LIPIcs paper. Its mortality result is an alternative proof of
Nuccio and Rodaro (2008), while its membership theorem is stronger. It concerns integer
matrices. Passing from a rational mortality instance to integer matrices by individually
clearing denominators preserves whether a product is zero, but it does not preserve the
unimodular hypothesis, so the theorem cannot be promoted to arbitrary rational families.
