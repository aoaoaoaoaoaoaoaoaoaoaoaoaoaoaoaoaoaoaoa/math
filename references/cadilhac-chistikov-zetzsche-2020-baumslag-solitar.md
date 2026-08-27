# Cadilhac, Chistikov, and Zetzsche (2020): Rational subsets of Baumslag–Solitar groups

**Citation.** Michaël Cadilhac, Dmitry Chistikov, and Georg Zetzsche, “Rational Subsets of
Baumslag–Solitar Groups,” in *47th International Colloquium on Automata, Languages, and
Programming (ICALP 2020)*, LIPIcs 168, article 116, 2020.
DOI: 10.4230/LIPIcs.ICALP.2020.116.

- Work identity: https://doi.org/10.4230/LIPIcs.ICALP.2020.116
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2020.116
- Local artifact: `cadilhac-chistikov-zetzsche-2020-baumslag-solitar.pdf`
- Version and status: peer-reviewed ICALP 2020 proceedings version, 16 pages
- Retrieved: 2026-08-07
- SHA-256: `ed88150c0c263c7d5a814ff3d33840f389a0d8b94c02c629c6aa9fe05e95db3f`
- Access and retention: Creative Commons Attribution 3.0; publisher PDF retained unchanged
- Synopsis basis: full-text inspection

## Synopsis

The group `BS(1,q)` is represented as the semidirect product `ℤ[1/q] ⋊ ℤ`, hence as affine maps
with one multiplicative base. The paper introduces pointed expansions: canonical annotated
base-`q` words encoding both the translation and exponent coordinates. A subset is PE-regular
when its pointed expansions form a regular language.

Theorem 3.1 proves that every rational subset of `BS(1,q)` is effectively PE-regular. Theorem 3.2
makes rational-subset membership PSPACE-complete, while Theorem 3.3 puts membership in each fixed
rational subset in logarithmic space. Proposition 3.6 proves effective Boolean closure of
PE-regular sets and closure under product and inverse; rational subsets themselves are not closed
under intersection.

The theorem applies to a single fixed base and a group language allowing inverses. It does not
decide arbitrary rational-affine semigroups with multiplicatively independent slopes or a
higher-dimensional projective action that has not been reduced to `BS(1,q)`.

## Source Assessment

The retained object is the peer-reviewed CC-BY proceedings paper. An arXiv long version,
arXiv:2006.11898v1, contains expanded proofs. No correction or retraction was found.

## Project Use

The `M₄(3)` audit uses this as a decidable retirement test for any proposed one-coordinate bridge
dynamics that truly closes inside a single-base affine group.
