# Separated Two-C Residue-Two Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

For every `k≥0`, both coupled width-three tag systems with separation

```text
n = 27k+2    and    n = 27k+20
```

halt from the queue `c bⁿ c bⁿ⁺¹`. These are two of the three subresidues of the last
previously open diagonal class `n≡2 (mod 9)`. This cut's sole survivor is `n≡11 (mod 27)`;
the subsequent `MM-S43` block macro reduces it further to `n≡38,65 (mod 81)`.

## Six-Event Macro

Put `n=3A-1`, so the coupled queue is

```text
P₀ = c b^(3A-1) c b^(3A).
```

For `A≡1 (mod 3)`, put `m=(4A-1)/3`. Five exact histories, each beginning with a `cbb`
stroke and followed by a computed unary `bbb` run, reach a queue with seven active `c`
letters. One further `cbb` step reaches a queue with eight `c` letters and run vector

```text
4A ; 3A-1 ; 4A+1 ; 3A-1 ; 3A+m+2 ; 3A-1 ; 4A+1 ; 3A-1 ; 3A.
```

Lean exposes the five intermediate queues and composes their exact reachability proofs. The
shared lemma for one macro executes

```text
c b^(3r+2) X  →*  X (bb c b^(3A-1) c b^(3A)) bʳ.
```

This avoids treating a long interactive trace as a proof.

## Phase Cut

Only letters at positions divisible by three can become deletion heads. For `A=9k+1`, the
eight final `c` letters occupy the two nonzero block phases and none is a head. For `A=9k+7`,
all eight occupy one nonzero phase and again none is a head. An offset-indexed invariant proves
these facts compositionally across the alternating unary runs and `c` letters. The standard
constant-head theorem then drains the queue because `b↦b` and each step deletes three letters.

Since

```text
A=9k+1  ⇒  n=27k+2,
A=9k+7  ⇒  n=27k+20,
```

both stated classes halt. When `A≡4 (mod 9)`, one later `c` returns to block phase zero, so
this certificate correctly leaves `n≡11 (mod 27)` unresolved at this stage. `MM-S43`
subsequently proves its `n≡11 (mod 81)` subresidue halts.

## Checked Boundary

[`MatrixMortality/SeparatedTwoCResidueTwo.lean`](../MatrixMortality/SeparatedTwoCResidueTwo.lean)
kernel-checks the exact event macros, the offset invariant, and the public theorems
`SeparatedTwoCResidue.twoModuloTwentySeven_tagHaltsFrom` and
`SeparatedTwoCResidue.twentyModuloTwentySeven_tagHaltsFrom`.

This result is only a diagonal congruence cut. It does not decide the surviving subresidue,
unequal separated runs, arbitrary two-`c` bodies, or deletion-width-three universality.
