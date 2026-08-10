# Gendler (2025): Partial results for union-closed conjectures on the weighted cube

**Citation.** Gabriel Gendler, “Partial Results for Union-Closed Conjectures on
the Weighted Cube,” arXiv:2504.13347v1, 2025.

- Work identity: [`arXiv:2504.13347v1`](https://arxiv.org/abs/2504.13347v1)
- Canonical source: https://arxiv.org/abs/2504.13347v1
- Local artifact: none; the arXiv non-exclusive distribution license does not grant downstream redistribution rights
- Version and status: arXiv v1 preprint
- Inspected: 2026-08-08
- Inspected PDF SHA-256: `2a36a8765708f63cbce630f0e02e6ccf8196195f2f9413a8248e7cf457f446e7`
- Access and retention: metadata only; arXiv non-exclusive distribution license 1.0
- Synopsis basis: complete full-text inspection of the six-page v1 PDF

## Synopsis

The paper extends Karpas’s Boolean-influence argument from uniform counting to a
product Bernoulli measure `μ_p` with coordinate parameters `p_i`. Writing
`p=min_i p_i` and `q=1−p`, Theorem 2.5 states that a simply rooted family `R`
with `μ_p(R)≤p` has a coordinate satisfying
`μ_p(R_i)≤p_i μ_p(R)`. By complementation, Theorem 2.6 says that a union-closed
family `G` with `μ_p(G)≥q` has a coordinate satisfying
`μ_p(G_i)≥(1−p_i)μ_p(G)`. At `p_i=1/2` this recovers Karpas’s half-cube theorem.

Section 3 also extends Knill’s logarithmic lower bound through weighted minimal
hitting sets. The resulting inequalities depend on the product weights and reduce
to Knill’s theorem in the uniform case.

## Source Assessment

The weighted Karpas proof is explicit and uses a consistent sign convention: the
indicator is `+1` on the simply rooted family. It therefore supplies an independent
reconstruction of the half-cube theorem while avoiding the directed-influence label
swap in Karpas’s original preprint. The theorem permits degenerate parameters in its
statement, but applications at boundary product measures still require the usual
nonempty/nontrivial checks. No peer-reviewed version was located.

## Project Use

Theorem 2.6 underlies the product-tilt attack: applied to the set-complement of an
intersection-closed family `F`, the condition `μ_p(F)≥max_i p_i` forces some
conditional inclusion probability in `F` to be at most `1−p_i`.
