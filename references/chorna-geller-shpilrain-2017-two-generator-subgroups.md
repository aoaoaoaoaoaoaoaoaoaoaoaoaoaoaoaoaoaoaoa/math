# Chorna, Geller, and Shpilrain (2017): Two-generator subgroups of `SL₂`

**Citation.** Anastasiia Chorna, Katherine Geller, and Vladimir Shpilrain, “On
two-generator subgroups in `SL₂(ℤ)`, `SL₂(ℚ)`, and `SL₂(ℝ)`,” *Journal of
Algebra* 478 (2017), 367–381.

- Work identity: DOI [`10.1016/j.jalgebra.2017.01.036`](https://doi.org/10.1016/j.jalgebra.2017.01.036)
- Canonical source: [author-hosted accepted manuscript](https://shpilrain.ccny.cuny.edu/2x2matrices.pdf)
- Local artifact: none; the operator excluded reference PDFs from Git
- Version and status: peer-reviewed publication; inspected author-hosted manuscript
- Retrieved: 2026-08-31
- Inspected artifact SHA-256: `f22e99e2d824f7ee8d062726a81bcc9b356c2176702aeb5e081ffffc0cbbefa9`
- Access and retention: author-hosted manuscript inspected transiently; not retained
- Synopsis basis: full-text inspection of the fourteen-page manuscript

## Synopsis

For

```text
A(k)=[[1,k],[0,1]],        B(k)=[[1,0],[k,1]],
```

Theorem 4 treats membership in `⟨A(k),B(k)⟩`. Its elementary operations are left
or right multiplication by `A(k)±¹` or `B(k)±¹`. For real `k≥2`, any sequence of
such operations which lowers the sum of the absolute matrix entries contains one
single lowering operation. For integral `k≥2`, an integral determinant-one matrix
at a local minimum is therefore either the identity or outside the subgroup.

Corollary 3 turns peak reduction into a membership algorithm for integral `k≥2`.
It decides membership and, on a positive instance, recovers the unique word in
time `O(n log n)`, where `n` is the sum of the absolute matrix entries. Theorem 3
also proves that for integral `k≥3` the generated subgroup has infinite index in
the displayed ambient congruence subgroup.

The paper's invariant is whole-matrix complexity. It does not state an orbit or
Borel-coset algorithm: many matrices can send one projective point to the same
target.

## Source Assessment

No correction affecting Theorem 4 or Corollary 3 was found. The paper measures
complexity by the magnitude of the matrix entries, not by input word length; its
`O(n log n)` claim must not be transferred to a point-orbit algorithm.

## Project Use

This is the closest peak-reduction prior art for `D2-D09`. The repository's
step-three pair-height theorem is separate: it proves finite reduced-syntax bounds
from a projective endpoint, whereas the paper decides membership of a supplied
complete matrix.
