# M₄(3) phase-zero right-`c` complement-blade audit

**Date:** 31 August 2026

**Status:** one exact modulo-sixteen blade removes half of the even/even complement states

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** expose arithmetic structure inside the mixed-body residue left after both unary rays

## Verdict

Define the complement coordinate

```text
D = S−C−1.
```

It is the ternary value of the zero digits in the native tag encoding and obeys the exact
append recurrences

```text
D(wc)=3D(w),
D(wb)=243D(w)+39.
```

Encoded length has the same residue modulo four as body length. Lean checks two integral
factorizations, for arbitrary integers `s,d,x,y,z`:

```text
H(16s+1, (16s+1)−(4d+2)−1, x,y,z) = 16Q₀+8,
H(16s+9, (16s+9)−4d−1, x,y,z)     = 16Q₂+8.
```

Consequently a body is excluded whenever

```text
length(body) ≡ 0 (mod 4) and D ≡ 2 (mod 4), or
length(body) ≡ 2 (mod 4) and D ≡ 0 (mod 4).
```

Inside the even-length, even-`b` rectangle, `D` is even. Any remaining zero must therefore
satisfy the compact necessary condition `D≡length(body) (mod 4)`. This removes, among others,
the shortest alternating bodies `bcbc` and `cbcb` for all waits.

## Proof Boundary

`ParabolicBlade.tagComplementCode_append_b`, `tagComplementCode_append_c`,
`tagEncode_length_mod_four`, and `tagComplementCode_mod_two` establish the physical coordinate
laws. `bridge_bZero_bTwo_cOne_det_ne_zero_of_complement_residue` transfers the two exact
integer factorizations through the checked determinant formula. No enumeration of bodies or
waits is used.

## Scope

The result treats deletion width three, exactly three atoms, orientation `0|2|1`, letters
`b|b|c`, and the stated infinite regular family of bodies. The congruence is a guillotine, not
a full classification: the complementary residue state still contains mixed bodies.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorem's transitive axiom set is recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
