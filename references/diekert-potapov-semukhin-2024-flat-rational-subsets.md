# Diekert, Potapov, and Semukhin (2024): Flat rational subsets of `GL₂(ℚ)`

**Citation.** Volker Diekert, Igor Potapov, and Pavel Semukhin, “Decidability of Membership
Problems for Flat Rational Subsets of `GL(2,Q)` and Singular Matrices,”
arXiv:1910.02302v6 [cs.FL], 28 November 2024.

- Work identity: https://doi.org/10.48550/arXiv.1910.02302
- Canonical source: https://arxiv.org/abs/1910.02302
- Local artifact: none; arXiv v6 uses only arXiv's nonexclusive distribution license
- Version and status: arXiv v6 preprint, substantially extending three conference papers
- Retrieved: 2026-08-07
- SHA-256: not applicable
- Access and retention: metadata-only record; arXiv v6 was inspected transiently
- Synopsis basis: full-text inspection of v6

## Synopsis

For a semigroup `M` and subsemigroup `S`, a flat rational subset is a finite union of products
`L₀g₁L₁⋯gₖLₖ` with each `Lᵢ` rational over `S`. The paper develops closure and membership
algorithms for this bounded-alternation class. Theorem 6.6 gives conditions under which flat
rational subsets over a subgroup form an effective relative Boolean algebra; Corollary 6.7
decides emptiness of Boolean combinations flat over `GL₂(ℤ)` inside `GL₂(ℚ)`.

Theorem 7.2 decides membership for `GL₂(ℚ)` automata flat over the monoid consisting of
`GL₂(ℤ)` and matrices of determinant magnitude greater than one, with a doubly exponential
upper bound. Theorems 8.1–8.2 extend the method to mortality and singular targets for specified
flat rational matrix families. Smith normal form and determinant growth bound how many
nonunimodular transitions a successful path can contain.

Theorem 5.4 gives a structural warning for groups strictly between `GL₂(ℤ)` and `GL₂(ℚ)`:
they are either a central free-abelian extension of `GL₂(ℤ)` or contain an infinite-index
extension of a Baumslag–Solitar group. General rational-subset membership beyond the flat class
is not decided.

## Source Assessment

Version 6 is a recent preprint with no journal reference on arXiv. It supersedes five earlier
revisions, so theorem numbers from older versions are unsafe. No correction or withdrawal was
found. Flatness means bounded alternation of rational strata; an unrestricted Kleene star over
several strata is not flat merely because each generator belongs to one of them.

## Project Use

The `M₄(3)` audit uses Theorems 6.6–8.2 only after a fixed residue skeleton or a target-content
bound has proved the bridge language flat. Unbounded alternating safe contexts remain outside
their scope.
