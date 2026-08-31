# M₃(4) Transverse Line-Atlas Hard-Core Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `4fe03da` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseLineHardCore.lean`](../MatrixMortality/TransverseLineHardCore.lean)

## Verdict

The finite rational `P¹` survivor of `G3-O27` contains the complete two-generator rational
projective-incidence core already in a single invariant plane. No chart switching or nontrivial
toggle is required. Consequently, a decision procedure for the unrestricted transverse atlas
would decide the `D2-S01` core and, through its separately audited reduction, `M₂(3)`.

This is a hardness embedding, not an undecidability theorem. `M₂(3)` remains open, and the result
does not reduce arbitrary multi-chart atlas reachability back to one `M₂(3)` instance.

## Exact Lift

Let `U : ℚ²→ℚ³` include the first coordinate plane and let `V : ℚ³→ℚ²` project onto it, so
`VU=I₂`. Given two rational matrices `A_b,A_c`, define

```text
D_b = U A_b V,        D_c = U A_c V,        T = I₃.
```

For a two-state row `r` and column `c`, define

```text
λ = rV,               γ = Uc.
```

Lean proves that both extensions are zero exactly when their two-state inputs are zero, so
nonzero projective endpoints remain nonzero.

Every `D_x` is singular because it kills the third basis vector. If `A_x` is invertible, Lean
proves

```text
rank D_x = 2,         im D_x = im U.
```

Thus the `M₂(3)` hard-core promise gives two exact rank-two data controls with one common image
plane and a matrix-level involutive toggle. Lean additionally identifies both the toggled and
untoggled `G3-O27` data carriers with that same plane. Every reachable lifted column remains in
it.

## Toggle Erasure And Orientation

Raw transverse words use the same left-action convention as `wordProduct`: the head control
multiplies on the left. The recursive map

```text
eraseToggles([]) = [],
eraseToggles(D_x :: w) = x :: eraseToggles(w),
eraseToggles(T :: w) = eraseToggles(w)
```

therefore deletes identity toggles without reversing the data word. Lean proves for every raw
word `w`

```text
D_w γ = U(A_eraseToggles(w)c),
λD_wγ = rA_eraseToggles(w)c.
```

The map sending a two-letter word to the same sequence of data controls is a section of
`eraseToggles`. Hence

```text
∃w : {D_b,D_c,T}*, λD_wγ = 0
  ↔ ∃u : {A_b,A_c}*, rA_uc = 0.
```

The empty word is included on both sides. Raw toggles create no additional zeros, and every
two-state witness has a toggle-free lifted witness.

## Relation To M₂(3)

`D2-S01` identifies the unresolved three-generator `2 × 2` mortality case with inputs

```text
A_b,A_c ∈ GL₂(ℚ),      r,c ≠ 0,
```

asking whether `rA_uc=0` for some two-letter word `u`. The formal lift accepts arbitrary
matrices and endpoints, but under this promise it is exactly that point-to-point reachability
problem on `P¹(ℚ)`. The formulas are finite rational matrix operations, so the transformation is
effective.

The formal file proves the scalar-incidence equivalence. The minimal-mortal-word case split and
rational-to-integer transport establishing the full `M₂(3)` equivalence remain audited under
`D2-S01`; this audit does not relabel them as formalized.

## Boundary Of The Cut

The embedding proves that the following restrictions do not make the general atlas survivor
easier than the dimension-two wall:

1. identity toggle;
2. two singular data maps of exact rank two;
3. one common invariant image plane;
4. no chart switching along the reachable orbit;
5. one source point and one terminal point;
6. arbitrary raw toggles allowed but algebraically erased.

A decidable atlas theorem must impose an additional restriction excluding some `D2-S01`
instance. Existing candidates include projective unimodularity, a preserved unordered pair,
group rather than positive-monoid reachability, or the valuation hypotheses of `D2-D05`–`D2-D08`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every two-state generator has a singular common-plane lift | promotion | Lean theorems `liftMatrix_det`, `liftMatrix_mulVec_mem_plane` |
| Invertible generators lift to exact rank two with image equal to the plane | promotion | Lean theorems `liftMatrix_rank_eq_two`, `liftMatrix_range_eq_plane` |
| Toggle erasure preserves word order and every scalar coefficient | promotion | Lean theorems `wordProduct_mulVec_liftColumn`, `linearCoefficient_eq` |
| Zero existence is equivalent for the lifted and two-state instances | promotion | Lean theorem `exists_zero_iff` |
| The full transverse atlas is no easier than the `D2-S01` core | promotion | exact computable subfamily embedding |
| The full atlas is equivalent to one `M₂(3)` instance | rejected | no reverse reduction for arbitrary chart switching is proved |
| `M₂(3)` is undecidable | rejected | no such theorem is known or implied |
| `M₃(4)` follows | rejected | the embedding supplies hardness, not a source-uniform paired recognizer |

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: any hope of deciding the unrestricted G3-O27 atlas while bypassing the dimension-two
         projective-incidence wall.
IDENTIFIED: one-chart transverse incidence and the D2-S01/M₂(3) hard core are the same exact
            instancewise zero-existence problem under the displayed lift.
SURVIVOR: solve the joint M₂(3) core, impose a strict decidable incidence stratum, or leave the
          singular/projectively-involutive atlas.
```
