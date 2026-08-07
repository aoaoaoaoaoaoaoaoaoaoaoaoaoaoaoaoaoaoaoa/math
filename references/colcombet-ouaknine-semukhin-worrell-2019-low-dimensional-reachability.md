# Colcombet, Ouaknine, Semukhin, and Worrell (2019): Low-dimensional reachability

**Citation.** Thomas Colcombet, Joël Ouaknine, Pavel Semukhin, and James Worrell,
“On Reachability Problems for Low-Dimensional Matrix Semigroups,” in *46th International
Colloquium on Automata, Languages, and Programming (ICALP 2019)*, LIPIcs 132,
article 44, 2019. DOI: 10.4230/LIPIcs.ICALP.2019.44.

- Work identity: https://doi.org/10.4230/LIPIcs.ICALP.2019.44
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2019.44
- Local artifact: `colcombet-ouaknine-semukhin-worrell-2019-low-dimensional-reachability.pdf`
- Version and status: peer-reviewed ICALP 2019 proceedings version, 15 pages
- Retrieved: 2026-08-07
- SHA-256: `714408f2674332da33ad2bab0a6ad4e7135c88ec41ad42cefb78cbfa85d6b3ef`
- Access and retention: Creative Commons Attribution 3.0; publisher PDF retained unchanged
- Synopsis basis: full-text inspection

## Synopsis

The paper studies membership and half-space reachability in two low-dimensional matrix
families. Theorem 7 decides membership in the integral Heisenberg group `H(n,ℤ)`, and
Corollary 8 extends this to `H(n,ℚ)` by clearing denominators and tracking the central
coordinate. The proof reduces the noncommutative product constraint to linear and quadratic
Diophantine conditions after separating whether generators with nonzero horizontal components
occur.

For `GL₂(ℤ)`, Sections 4–5 use canonical words for the modular group. Theorem 16 proves that
for rational vectors `u,v` and rational `λ`, the set
`{M ∈ GL₂(ℤ) | uᵀMv ≥ λ}` is a regular subset of `GL₂(ℤ)`. Intersecting its canonical-word
language with the regular language of generator products yields decidability of half-space
reachability in Theorem 17. Theorem 20 separately decides half-space reachability in
`H(n,ℚ)`.

The two-dimensional result requires unimodular integral matrices. It does not decide scalar or
half-space reachability for arbitrary rational or determinant-growing `2 × 2` semigroups.

## Source Assessment

The retained object is the peer-reviewed proceedings version and identifies a longer arXiv
version, arXiv:1902.09597. No correction or retraction was found. The regular-language theorem
is exact for `GL₂(ℤ)`; extending it to a rational semigroup requires an additional normalization
or bounded nonunimodular-factor argument.

## Project Use

The `M₄(3)` literature audit uses Theorems 16–17 as the exact unimodular core of a proposed
determinant/content stratification, with the stated scope barrier retained.
