# Physical Role-Block Shell Completion Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every physical swapped role block supplies the arithmetic hypotheses of the
first-multi extinction theorem

This audit removes the expected-shell and lower-unit assumptions retained by
[`MM-S51`](../SALVAGE.md#mm-s51-double-deletion-ratio-chamber-extinction). It also identifies
literal `D_c` as the only physical first block outside the nontrivial-depth interface.

## Lower Unit

A role block has the form `front·D_x`. The last lower image is the one-bit word `0`, whose
swapped ternary digit is two. Therefore

```text
V_z≡2 (mod 3),                                           (1)
```

and the rational integer cast of `V_z` is a `3`-adic unit. This argument is independent of the
block length, phase history, compiler body, and final erased letter.

## Multi-Role Depth

If the block has at least two roles, the preceding role's lower image also ends in `0`. Its
swapped lower spelling consequently ends in `[1,1]`, whose two low ternary digits are `22`.
The punctuated swapped upper word ends in the same two digits because `β≥2` and the marker is
`10^β`. Hence

```text
P_z≡8 (mod 9),       V_z≡8 (mod 9).                     (2)
```

Put `ρ=3^β`, `R=2−ρ`, and `H=5ρ−1`. Modulo nine, `R≡2` and `H≡8`, so

```text
C_z=RP_z−HV_z≡2·8−8·8≡6 (mod 9).                       (3)
```

Thus three divides `C_z` and nine does not. Lean factors an arbitrary integer satisfying (3)
as three times a unit and proves

```text
v₃(C_z)=1.                                              (4)
```

## Singleton Depth

A singleton role block ending in an erasure is exactly `D_b` or `D_c`. Their closed centered
coefficients are

```text
C_Db=−ρ(18ρ²−40ρ+17),
C_Dc=−ρ(5ρ−1).                                         (5)
```

Both cofactors are two modulo three. Since `ρ=3^β`, equation (5) gives exact valuation `β`.
Together with (1), equations (2)-(5) prove `roleBlock_arithmeticShell`: every physical block
has an existential depth satisfying its `HasPoleShell`, coefficient `HasValue`, and lower-code
`IsUnit` contracts.

## Initial Block

Every Neary upper image is nonempty, so the number of roles is at most the upper spelling
length. A nonsingleton role block therefore has upper length at least two. For a singleton,
`D_c` has upper length one and `D_b` has upper length `β+2`. Lean proves the exact implication

```text
first≠D_c  →  1<upperLength(first).                     (6)
```

`physicalFirstMultiTransfer_pole_false` uses (6) and two applications of
`roleBlock_arithmeticShell` to discharge every shell, coefficient, unit, and nontrivial-depth
hypothesis of `firstMultiTransfer_pole_false`. Its remaining assumptions are the compiler body
envelope, three physical role blocks, `first≠D_c`, and the exact centered two-step pole equation.

## Boundary

This result completes the local physical interface but does not justify reusing it at an
arbitrary later history. A later earliest pole starts from a general centered fold state, not
necessarily the special state `(3^m, R·P)` produced by one first block. No checked theorem
currently reinitializes such a state by sliding the two-block window. The remaining master
target is therefore a genuine history theorem: classify the earliest zero denominator in the
fold from the ordinary reset and prove it is terminal.

## Verification

[`SwappedSetterPhysicalShell.lean`](../MatrixMortality/SwappedSetterPhysicalShell.lean) contains
the complete suffix, congruence, valuation, length, and shell-free composition proofs. The
module builds warning-free and contains no proof aperture. An independent formalization and a
separate audit obtained the same mod-nine residues, singleton factors, and initial-block
dichotomy. Lean LSP reports zero diagnostics. Publication-facing declarations are listed in
`AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterPhysicalShell.lean`](../MatrixMortality/SwappedSetterPhysicalShell.lean)
- [`MM-S51`](../SALVAGE.md#mm-s51-double-deletion-ratio-chamber-extinction)
- [`MM-S55`](../SALVAGE.md#mm-s55-physical-role-block-shell-completion)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
