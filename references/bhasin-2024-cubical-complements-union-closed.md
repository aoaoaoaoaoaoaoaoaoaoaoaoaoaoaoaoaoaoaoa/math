# Bhasin (2024): A cubical perspective on complements of union-closed families

**Citation.** Dhruv Bhasin, “A Cubical Perspective on Complements of
Union-Closed Families of Sets,” arXiv:2409.17050v1, 2024.

- Work identity: [`arXiv:2409.17050v1`](https://arxiv.org/abs/2409.17050v1)
- Canonical source: https://arxiv.org/abs/2409.17050v1
- Local artifact: `bhasin-2024-cubical-complements-union-closed.pdf`
- Version and status: arXiv v1 preprint
- Retrieved: 2026-08-08
- SHA-256: `55810690d595f479dd879f8bec93e9eb41223852b8f1e2de3dbb69511c08f07b`
- Access and retention: CC BY 4.0, stated on the arXiv record
- Synopsis basis: complete full-text inspection of the 13-page v1 PDF

## Synopsis

For a set family `F⊆2^[n]`, the paper forms the induced cubical complex `X(F)` whose
cells are Boolean intervals `[A,B]` contained in `F`. Theorem 1.1 proves that `X(F)` is
acyclic whenever `F` is simply rooted and contains the empty set. Corollary 1.2 gives the
Euler identity

```text
Σ_{k=0}^n (−1)^k |C_k(F)| = 1,
```

where `C_k(F)` is the set of `k`-dimensional Boolean intervals contained in `F`.
Corollary 2.17 gives the corresponding Euler characteristic when the empty set is absent.

The proof removes a maximum member, expresses its cubical star through its root
intervals, and glues acyclic subcomplexes along an explicitly acyclic intersection. The
map `φ(A)`, the union of complement members below `A`, identifies the roots of `A` as
`A∖φ(A)`. The project's cubical audit observes that every piece and intersection in the
induction is contractible, so the same proof establishes contractibility.

## Source Assessment

The paper supplies a topological invariant for complements of union-closed families but
does not derive a frequency bound. Definition 2.1 contains a material typographical error:
it prints `[i,A]⊆2^[n]` where the standard and subsequently used condition is
`[i,A]⊆F`. The proof of Theorem 1.1 also writes `X(F∖{A})` once in a case where the
argument requires `X(F_A∖{A})`. Finally, the proof of Lemma 2.16 invokes Proposition
2.15 outside its hypothesis when `φ(A)=∅`; in that case `[∅,A]` is a full cube and
gives the required alternating cancellation directly. These repairs are forced by the
surrounding definitions and proof, but downstream reliance should cite them explicitly. No
later version was available at inspection.

## Project Use

The contractibility and Euler identity are candidate global constraints on the simply rooted
cube complement of a hypothetical Frankl counterexample. The
[`unique-root audit`](../audits/frankl-cubical-unique-roots-2026-08-08.md) identifies the
downward edge boundary in [`FC-S02`](../SALVAGE.md#fc-s02-downward-boundary-obstruction)
with the number of uniquely rooted vertices and proves the quantitative lower bound that a
counterexample would have to satisfy.
