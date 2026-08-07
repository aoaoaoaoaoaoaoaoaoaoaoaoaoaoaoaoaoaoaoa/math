# M₄(3) safe-return audit

**Date:** 6 August 2026

**Status:** residue-zero safe bridges excluded; arbitrary safe return and `M₄(3)` remain open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide whether a nonempty regular safe bridge can be singular, and consume that
decision in the first-residue-two problem

## Verdict

The external report correctly exhibits actual two-letter residue-zero safe states converging
`3`-adically to the bridge-singularity wall. This rules out a proof based only on finitely many
local `3`-adic digits or truncated valuations. That lane was already excluded by the frontier,
and the report proves no exact safe return, one-defect theorem, malformed zero, or reduction.

Formalization produced a stronger Archimedean result from the same family. Every nonempty
regular bridge whose atoms all have residue zero has strictly negative determinant. Therefore
every singular nonempty safe bridge, if one exists, contains a regular residue-one atom. The
proof is an arbitrary-length cone induction, not a bounded search.

No Lean API was added. The cone theorem removes one infinite sector of the live return problem,
but the first consuming theorem still needs arbitrary residue-one occurrences. Encoding the
recurrence before that consumer exists would enlarge the formal surface without changing the
master obstruction.

## External Claim Audit

The shared conversation received the intended 11,560-byte prompt and reproduced its prompt ID
and source commit. Its formulas were reconstructed from the pinned atom definitions.

Let

```text
C = Q(c,0) = [[1,2,2], [0,3,0], [0,0,3]],
Uⱼ = Q(b,3j)
   = [[1,(15ρ+1)/2,2+48j], [0,9ρ,0], [0,0,3+24j]],
Mⱼ = C Uⱼ.
```

For `k=(4,4,-1)ᵀ` and `n=(22,-31,-36)`, exact multiplication gives

```text
adj(Mⱼ)k = 3wⱼ,

wⱼ = (90ρ-6+48j(21ρ-1), 12+96j, -9ρ)ᵀ,
n wⱼ = 72Dρ(j),
Dρ(j) = 32ρ-7+4j(77ρ-14),
det K(Mⱼ) = -243ρDρ(j).
```

Both coefficients of `Dρ(j)` are positive for `ρ≥1`, so no natural `j` returns. Its slope is a
`3`-adic unit when `ρ=3^β`, however, and the unique `3`-adic root is

```text
j* = -(32ρ-7)/(4(77ρ-14)) ∈ ℤ₃,       -1 < j* < 0.
```

Natural representatives of `j* mod 3ᴺ` consequently produce actual safe states approaching the
return wall to arbitrary `3`-adic precision. This is correct, but it distinguishes no exact
natural execution and does not alter the master frontier.

The reported chart pole is also exact:

```text
C⁻¹k = (2,4/3,-1/3)ᵀ.
```

The chart coordinate `Y+4Z` vanishes there although the return covector does not. This rejects
that single chart, not a two-chart or coordinate-free proof.

## Residue-Zero Cone

Use the checked triangle coordinates, where

```text
det K(W) = (9ρ/2)u(W),
(u,v,w)(I) = (0,22,9).
```

Consider the cone

```text
u ≤ 0,       v > w > 0.                                (C)
```

The initial state lies in `(C)`. Both residue-zero transitions send `(C)` into its strict
interior in the `u` coordinate and preserve `v>w>0`.

For `Q(b,3j)`, `j≥0`, the decisive differences are

```text
v'-w' = (9ρ/2)((24j+5)v-2w) > 0,

u' = 3u -(9/2)(2ρ-1)v +3(1-3ρ)w
   + j(24u-36(4ρ-1)v+24w) < 0.
```

Here `ρ=3^β≥1`, `u≤0`, and `w<v`; every displayed constant and wait contribution has the
required strict sign. The formula for `w'` is a positive combination of `v,w`.

For `Q(c,3j)`, `j≥0`, set

```text
A=(M-3)j+3,       B=(L-1)j+1.
```

From `M=27Π` and `(45Π+5)/2≤L≤M-2`, the Neary bounds imply

```text
2M-L-5 > 0,       3L-2M > 0,       M>3,       L>1.
```

Therefore

```text
v'-w' = (3/2)(2A-B)v-3w > 0,

u' = 3u-(3/2)v
   + j((M-3)(u+w)-(3/2)(L-1)v) < 0.
```

Indeed, `2A-B=(2M-L-5)j+5`; and `u+w<v` while
`M-3 < (3/2)(L-1)` follows from `2M<3L`. Again `w'>0` directly.

Induction over the right-to-left atom action now proves

```text
W nonempty and every gap of W is 0 mod 3
    → u(W)<0
    → det K(W)<0.
```

Thus a singular nonempty regular safe bridge must contain a residue-one atom.

## Disposition

| Claim | Disposition |
| --- | --- |
| Fixed projective incidence for bridge singularity | restatement of the audited triangle wall |
| Pole of the single `Y+4Z` chart at `Q(c,0)` | correct local diagnostic; culled |
| Two-letter residue-zero orbit accumulates on the wall over `ℚ₃` | correct; confirms an already killed local-valuation lane |
| Finite local `3`-adic data cannot by itself decide exact return | correct at the stated locally constant scope; not a master cut |
| Every nonempty residue-zero regular safe bridge has negative determinant | new audited arbitrary-length cut |
| Safe-bridge invertibility, single-defect nonvanishing, or `M₄(3)` | open |

## Exact Wound

```text
MASTER VERDICT: still open
REMOVED: singular nonempty safe bridges containing only residue-zero atoms
REMAINS: safe return with at least one regular residue-one atom; then the arbitrary-context
         one-defect sandwich and successive defects
DISTANCE: decide the residue-one skeleton after compressing intervening residue-zero runs,
          or bypass safe return by deciding the one-defect bridge language directly
```
