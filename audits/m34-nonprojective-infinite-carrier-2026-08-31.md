# M₃(4) Nonprojective Infinite-Carrier Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `d5d46ec` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseInfiniteAtlas.lean`](../MatrixMortality/TransverseInfiniteAtlas.lean)

## Verdict

The finite-carrier conclusion of `G3-O27` fails sharply when the toggle is not projectively
involutive. One rational diagonal toggle with three distinct eigenvalues sends an explicit
rank-two data image through infinitely many pairwise distinct rational planes. The planes arise
from literal raw prefixes and persist for every value of a rational source parameter.

This proves that the nonprojective structural escape is real. It does not provide a terminal row,
a paired same-zero recognizer, or an undecidability reduction.

## Matrices

Fix

```text
T = diag(1,2,3),

      [ 1   s   0 ]
D_s = [−1   0   0 ],            s∈ℚ.
      [ 0  −1   0 ]
```

Lean factors `D_s` through a split two-dimensional interface. A left inverse and right inverse
certify

```text
rank D_s = 2,           det D_s = 0
```

for every `s`. It also proves

```text
Tⁿ = diag(1,2ⁿ,3ⁿ),     det T = 6.
```

The diagonal entries of `T²` are `1,4,9`, so Lean proves `T²≠qI` for every `q∈ℚ`. Thus the
example lies exactly outside the matrix hypothesis of `G3-O27`, not in an unexamined degeneracy
of it.

## Carrier Orbit

Let

```text
C_n(s) = im(TⁿD_s).
```

Left multiplication by `Tⁿ` preserves rank because its determinant is nonzero, so every `C_n(s)`
is a plane. Lean proves the complete action formula

```text
TⁿD_s(x,y,z) = (x+sy, −2ⁿx, −3ⁿy).
```

Consequently the integral row

```text
N_n(s) = (6ⁿ,3ⁿ,s·2ⁿ)
```

annihilates all of `C_n(s)`. The first input basis vector produces

```text
v_n = (1,−2ⁿ,0) ∈ C_n(s).
```

If `n<m`, then

```text
N_m(s)·v_n = 6^m − 3^m2ⁿ = 3^m(2^m−2ⁿ) > 0.
```

Hence `v_n∉C_m(s)`, so `C_n(s)≠C_m(s)`. Lean proves the resulting map

```text
n ↦ C_n(s)
```

injective for every rational `s`.

## Raw-Word Orientation

The control word

```text
tⁿb = [t,…,t,b]
```

contains `n` leading toggles followed by one data control. With the repository's head-left
`wordProduct` convention, Lean proves its product is exactly

```text
TⁿD_s,
```

not `D_sTⁿ`. The same `D_s` is assigned to both data letters only to keep the counterexample
minimal; the `b` prefix alone witnesses the infinite carrier orbit.

## Scope

The result is uniform in the parameter `s`, which may be computed from `(β,body)` or any other
source description. Uniformity does not make it a compiler. No theorem identifies a fixed row
whose intersections with these planes equal the unrestricted paired terminal language, and no
arbitrary-word same-zero converse is claimed.

The example settles only existence of infinite carrier closure. A complete classification of
diagonalizable toggles would additionally distinguish invariant coordinate planes, periodic
subspaces caused by eigenvalue ratios that are roots of unity, and generic infinite orbits.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `D_s` has exact rank two for every rational `s` | promotion | Lean theorem `data_rank_eq_two` |
| `T` has three distinct rational eigenvalues and non-scalar square | promotion | explicit diagonal form and Lean theorem `toggle_sq_ne_smul_one` |
| Every raw-prefix carrier retains rank two | promotion | Lean theorem `carrierMatrix_rank_eq_two` |
| `N_n(s)` annihilates `C_n(s)` | promotion | Lean theorem `normal_dotProduct_carrierMatrix_mulVec` |
| The carrier-plane orbit is injectively infinite | promotion | Lean theorems `carrier_ne_of_lt`, `carrier_injective` |
| Literal prefixes realize the displayed product orientation | promotion | Lean theorem `wordProduct_carrierWord` |
| Nonprojective toggles yield a paired recognizer | rejected | no terminal row or source-zero equivalence is constructed |
| Every nonprojective toggle has infinite carrier closure | rejected | special invariant or periodic subspaces may have finite orbit |
| `M₃(4)` follows | rejected | infinite geometry alone does not recognize the source language |

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: finite-carrier closure as a consequence of singular data plus rational diagonalizable
         toggle dynamics.
CONSTRUCTED: an explicit source-parameter, exact-rank-two, injectively infinite carrier-plane
             orbit realized by raw prefixes.
SURVIVOR: make one source-computable row exploit this depth on every raw word, or classify and
          obstruct the resulting infinite terminal arithmetic.
```

