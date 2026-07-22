# Halava–Harju–Hirvensalo (2007)

**Citation.** Vesa Halava, Tero Harju, and Mika Hirvensalo, “Undecidability Bounds
for Integer Matrices Using Claus Instances,” *International Journal of Foundations of
Computer Science* 18(5):931–948, 2007.

- DOI: https://doi.org/10.1142/S0129054107005066
- Canonical author copy: https://users.utu.fi/harju/articles/HHH_ClausInst.pdf
- Local PDF: `halava-harju-hirvensalo-2007-claus-instances.pdf`
- Retrieved: 2026-07-21
- SHA-256: `e99e9841ac7a4a41bd0067e2d8e0a29667d87e9276599bb16048f80a7f4bc20c`

## Results used

- Lemma 1 and Theorems 2–6 use *Claus instances*, whose nonempty solutions have a
  distinguished first tile and distinguished final tile.
- Theorem 10 absorbs those endpoint matrices into the idempotent rank-one matrix
  `B = E₁₁`: the seven mortality generators are `BM₁, M₂, …, M₆, M₇B`.
- Its converse expands any product containing `B` into a product of `(1,1)` scalars,
  closely anticipating the scalar-factor argument in the present five-matrix proof.

## Audit notes

This is the closest prior art found for endpoint absorption. It does **not** imply the
present result directly. Its generator saving relies on both endpoint tiles being absent
from the interior, whereas tile 1 in Neary's five-pair construction can recur internally.
The present construction needs only a forced final tile: it replaces `X₅` by `X₅E₃₁` and permits that
same rank-one generator to serve as both delimiters. In fixed-boundary GPCP language this is
the standard outer-product separator, so the algebraic device is old. What was not found here
is the source observation that the corrected terminal family is an undecidable four-generator
GPCP family, and hence yields the valid `M₃(5)` bound.
