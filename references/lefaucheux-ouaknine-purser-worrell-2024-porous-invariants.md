# Lefaucheux, Ouaknine, Purser, and Worrell (2024): Porous invariants

**Citation.** Engel Lefaucheux, Joël Ouaknine, David Purser, and James Worrell, “Porous
Invariants for Linear Systems,” *Formal Methods in System Design* **63** (2024): 235–271.
DOI: 10.1007/s10703-024-00444-3.

- Work identity: https://doi.org/10.1007/s10703-024-00444-3
- Canonical source: https://link.springer.com/article/10.1007/s10703-024-00444-3
- Local artifact: `lefaucheux-ouaknine-purser-worrell-2024-porous-invariants.pdf`
- Version and status: peer-reviewed version of record, 37 pages
- Retrieved: 2026-08-07
- SHA-256: `283c3bae3152f45577f8cb3394160e254ebdd09b29011e3fa4b8ef4e6e1b3192`
- Access and retention: Creative Commons Attribution 4.0; publisher PDF retained unchanged
- Synopsis basis: full-text inspection

## Synopsis

The paper develops inductive invariants for nondeterministic integer linear dynamical systems,
using arithmetic sets that may be disconnected or nonconvex. Theorem 10 computes in polynomial
time the strongest `ℤ`-linear inductive invariant containing a multipath orbit. For deterministic
systems and an unreachable point, Theorem 19 effectively constructs a separating
`ℕ`-semilinear invariant.

The nondeterministic boundary is sharp. Theorem 21 proves undecidability of whether a separating
`ℕ`-semilinear invariant exists, already for 13 matrices in dimension 7 or two matrices in
dimension 91. In contrast, Theorem 22 decides reachability for a finite family of one-dimensional
integer affine maps and constructs a separating semilinear invariant in unreachable instances.
Theorem 37 decides reachability of a full-dimensional `ℤ`-linear target for arbitrary multipath
systems, while Theorem 40 gives low-dimensional deterministic results for semilinear targets.

The accompanying `porous` tool implements the one-dimensional affine and selected lattice-target
procedures. Its output proves inductiveness of a semilinear overapproximation; it is not a general
oracle for low-dimensional hyperplane reachability.

## Source Assessment

The retained object is the open-access version of record. No correction or retraction was found.
The distinction between `ℤ`-linear, `ℕ`-semilinear, deterministic, nondeterministic, point, and
full-dimensional targets is essential: the paper contains both algorithms and undecidability
results across those boundaries.

## Project Use

The `M₄(3)` audit uses Theorem 10 as an exact first invariant-synthesis pass and Theorems 21–22 as
the boundary against assuming that a useful multipath semilinear separator must exist.
