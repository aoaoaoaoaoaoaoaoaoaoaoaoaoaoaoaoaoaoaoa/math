# Karpas (2017): Two results on union-closed families

**Citation.** Ilan Karpas, “Two Results on Union-Closed Families,”
arXiv:1708.01434v1, 2017.

- Work identity: [`arXiv:1708.01434v1`](https://arxiv.org/abs/1708.01434v1)
- Canonical source: https://arxiv.org/abs/1708.01434v1
- Local artifact: none; the arXiv non-exclusive distribution license does not grant downstream redistribution rights
- Version and status: sole arXiv version; unpublished preprint
- Inspected: 2026-08-08
- Inspected PDF SHA-256: `2c190f29b4b4a307e93a9d363548e8664c5a8b60492295e92fdab7bc94a4c9e4`
- Access and retention: metadata only; arXiv non-exclusive distribution license 1.0
- Synopsis basis: complete full-text inspection of the 13-page v1 PDF and independent reconstruction of Theorem 1.2

## Synopsis

Theorem 1.2 proves Frankl’s conjecture for every union-closed family
`G ⊆ 2^[n]` of cardinality at least `2^(n−1)`. The complement `R=2^[n]∖G`
is *simply rooted*: every `A∈R` has an `i∈A` for which every set between
`{i}` and `A` lies in `R`. A Boolean-influence argument shows that a simply
rooted family of size at most half the cube has a coordinate occurring in at
most half its members.

Theorem 1.3 bounds by `2^(n−1)` the number of sets outside a union-closed
family which cover one of its sets. Combining this with the FKN and
Kindler–Safra concentration theorems, Theorem 1.4 extends the density threshold
to `(1/2−c)2^n` for an unspecified absolute `c>0`.

## Source Assessment

The half-cube theorem is independently repairable and is repeatedly cited in
later literature, but the preprint was not located in a peer-reviewed venue.
The displayed definitions and Observation 2.2 interchange the labels on the
two directed influences: with `f=−1` on the simply rooted family and
`χ_i(x)=(−1)^{x_i}`, the correct identity is
`f̂({i})=I_i^−−I_i^+` under the displayed edge definitions, and Lemma 2.8
bounds that same `I^−`, not `I^+`. Consistently swapping the two labels repairs
the proof verbatim. The numerical statement and the polarity needed by its
applications are unaffected.

## Project Use

Theorem 1.2 supplies the density dichotomy proving Frankl’s conclusion for
every bidual Horn Boolean function. The source’s influence-label defect is kept
explicit so the project does not cite the printed algebra without repair.
