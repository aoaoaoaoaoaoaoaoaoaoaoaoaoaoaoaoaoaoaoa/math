# M₄(3) phase-zero right-`c` zero-wait complement audit

**Date:** 31 August 2026

**Status:** complement density at least `1/585` makes the zero-wait core positive

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** remove the zero middle-wait face from dense first-`b` cylinders

## Verdict

For rational `S,D` with `S>1`, `D>0`, and `S−1≤585D`, Lean proves

```text
H(S,S−1−D,x,0,z)>0
```

for every natural `x,z`.

## Proof Boundary

The core is collected into a positive constant plus `x` times a slope. The sole comparison is

```text
Jx−585·9A = 266586336z+28363176>0.
```

The density hypothesis transfers this strict gap to the slope; all remaining factors are
positive. No body enumeration or approximate arithmetic enters the proof.

## Scope

This theorem treats only `y=0` in the primitive phase-zero right-`c` core. It is a reusable
face obstruction, not a full body-family extinction.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The theorem's
transitive axiom set is recorded in `verification/axioms.txt`. No proof aperture, external
declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
