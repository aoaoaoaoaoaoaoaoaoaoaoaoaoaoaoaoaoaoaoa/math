# Protasov (2025/2026): Perron matrix semigroups

**Citation.** Vladimir Yu. Protasov, “Perron Matrix Semigroups,”
arXiv:2502.10571v2 [math.RA], revised 12 May 2026.

- Work identity: https://doi.org/10.48550/arXiv.2502.10571
- Canonical source: https://arxiv.org/abs/2502.10571
- Local artifact: `protasov-2026-perron-matrix-semigroups-v2.pdf`
- Version and status: arXiv v2 preprint; v1 submitted 14 February 2025
- Retrieved: 2026-08-07
- SHA-256: `c561a53a16c29acb54a90e6bd4ece5e172a3a33b9a584e14b90a623fc85210d0`
- Access and retention: Creative Commons Attribution-NonCommercial-ShareAlike 4.0; PDF retained unchanged
- Synopsis basis: full-text inspection of v2

## Synopsis

A real matrix semigroup is called Perron when every element has a nonnegative eigenvalue equal to
its spectral radius. Every semigroup preserving a proper convex cone is Perron. The paper studies
the converse under irreducibility and introduces the semigroup index, the least geometric index
among its elements.

Theorem 1 proves that an irreducible Perron semigroup has a common invariant cone unless its index
is at least three. Theorem 2 rules out irreducible Perron semigroups of index two. Theorem 3
classifies the low-dimensional cases: in dimensions two and four, irreducible Perron semigroups
are exactly those with an invariant cone; in dimension three, the only additional class is
proportional to a subgroup of `SO(3)`. The paper also constructs higher-dimensional exceptions
and identifies remaining classification problems.

The criteria quantify over the entire generated semigroup: checking only the finite generating
set for Perron eigenvalues is insufficient. The paper does not give a general finite algorithm
for deciding that every product is Perron or for constructing the common cone from arbitrary
rational generators.

## Source Assessment

This is a recent, unrefereed preprint. Version 2 supersedes v1 and adds the stated low-dimensional
classification; the local filename records that version explicitly. No independent correction
was found. Any use must retain irreducibility, whole-semigroup Perronness, and index hypotheses.

## Project Use

The `M₄(3)` audit uses Fact 1 to exclude a finite componentwise proper-cone system for one repeated
exterior atom whose spectral-radius eigenvalues are nonreal. It does not treat the paper as an
algorithm for constructing or deciding cones.
