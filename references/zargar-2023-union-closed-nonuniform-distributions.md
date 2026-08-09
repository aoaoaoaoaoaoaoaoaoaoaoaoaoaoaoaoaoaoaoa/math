# Zargar (2023): The union-closed sets conjecture for non-uniform distributions

**Citation.** Masoud Zargar, “The Union-Closed Sets Conjecture for Non-Uniform
Distributions,” arXiv:2305.19338v2, 2023.

- Work identity: [`arXiv:2305.19338v2`](https://arxiv.org/abs/2305.19338v2)
- Canonical source: https://arxiv.org/abs/2305.19338v2
- Local artifact: `zargar-2023-union-closed-nonuniform-distributions.pdf`
- Version and status: arXiv v2 preprint
- Retrieved: 2026-08-08
- SHA-256: `f8e536a627da8ae5357f6cff45d1e8c40d9a838ce48974a71e8c10d3b418976b`
- Access and retention: CC BY 4.0, stated on the arXiv record
- Synopsis basis: complete full-text inspection of the 15-page v2 PDF and its TeX source

## Synopsis

The paper replaces each Boolean zero by `k` nilpotent labels and each Boolean one by
`m` cyclic-group labels. An intersection-closed family lifts to a finite
multiplication-closed set, so entropy cannot increase under independent multiplication.
Theorem 1.3 proves that, for coordinatewise integers `k_i≥5` and
`1≤m_i≤√k_i`, every intersection-closed family has a coordinate omitted with
conditional weight at least one half under weights

```text
weight(A) = ∏_{j∈A} (m_j/k_j).
```

In the homogeneous case this is a Maxwell–Boltzmann distribution proportional to
`t^|A|`, with `t=m/k≤1/√k`. The proof reduces the entropy increment to a functional
`F_{k,m}` on probability measures of fixed mean, proves that functional concave for
`k≥3`, reduces its minima to three two-point types, and checks positivity in the stated
parameter range.

The introduction isolates `k=2,m=1`, corresponding to homogeneous weight `t=1/2`, as
an untreated boundary. It says that the half-frequency conclusion would follow if the
concavity argument for `F_{2,1}` could be supplied. The published concavity calculation
divides by `k(k−1)/2−1`, which vanishes exactly at `k=2`.

## Source Assessment

The non-uniform theorem is explicit but was not located in a peer-reviewed venue. It is
not a statement at the uniform distribution: the smallest inverse temperature covered is
`log(5/2)`. The `k=2` seam is a genuine removable-singularity problem in the kernel
rather than a numerical optimization claim. It is closed by the project's
[`k=2,m=1` audit](../audits/frankl-binary-semigroup-kernel-2026-08-08.md), which proves
the sharp functional lower bound and the resulting weighted half-frequency theorem. The
paper does not discuss Gendler’s later weighted half-cube theorem.

## Project Use

The semigroup lift is a distinct bridge between closure and entropy. The audited `k=2`
theorem supplies a rigorous homogeneous-tilt endpoint at weight `1/2`; the larger question is
whether it can be transported toward uniform weighting without reintroducing the known
binary-entropy barrier.
