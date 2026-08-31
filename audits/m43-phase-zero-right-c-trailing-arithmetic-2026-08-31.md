# M₄(3) phase-zero right-`c` trailing-arithmetic audit

**Date:** 31 August 2026

**Status:** exact complement valuation and primitive cross-resultant are formalized

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace the erroneous unreduced Hensel lower bound by lawful trailing arithmetic

## Verdict

For a last `b` followed by exactly `h` trailing `c` letters, Lean proves

```text
D=3^(h+1)(81D₀+13),
(81D₀+13) mod 3=1.
```

The two affine `z` pencils `P=Az+B` and `K=Cz+E` satisfy

```text
AE−CB=2·3^12(48x−3029)(674088x−4333144y−1095244575).
```

The trailing scale also separates exactly from the core:

```text
H=r((72y−9)PS₀+12KD₀)−(8y−9)P.
```

## Proof Boundary

The complement formula is an induction over right-appended `c` letters after the final `b`.
The cofactor congruence is exact natural arithmetic. The primitive-pencil collection,
cross-resultant, and scaled-core decomposition are polynomial identities over commutative rings
or the integers.

No bounded classifier is promoted here. In particular, the false inference from
`z≡7381+59049x (mod 177147)` to `z≥7381+59049x` is absent: congruences must first be reduced.

## Scope

These identities concern the deletion-width-three, three-atom, phase-zero right-`c` primitive
core. They do not yet prove a maximum trailing-run length.

## Validation

`MatrixMortality.ParabolicTrailing` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicTrailing.lean`](../MatrixMortality/ParabolicTrailing.lean)
