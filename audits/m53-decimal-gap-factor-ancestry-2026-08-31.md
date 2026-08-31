# Decimal Setter Gap-Factor Ancestry Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** gap-prime support has an exact lower-code ancestry and every still-clean factor
imposes two singleton congruences; those congruences are jointly attainable by a physical
all-deletion word and do not close the setter

This audit intersects the abstract long singleton carriers of
[`MM-S20`](../SALVAGE.md#mm-s20-singleton-carrier-classification) with the denominator ancestry
of [`MM-S17`](../SALVAGE.md#mm-s17-recursive-decimal-carrier). It does not settle `M₅(3)`.

## Physical Factors

For width `β>0`, put

```text
q=2·10^β−7,       E=9q,       G=502·10^β−7.
```

The power `10^β` is one modulo nine, so `G=9g` for an integer `g`. The primitive gap factor is
coprime to the lift and to the lower digit of either singleton erasure:

```text
gcd(q,G)=gcd(q,7)=1.                              (1)
```

For the first equality, `G=251q+1750`. The integer `q` is odd, is three modulo five, and is
coprime to seven because `10` is; hence it is coprime to `1750=2·5³·7`. Both singleton
erasures have lower word `[false]`, whose decimal code is `7`.

## First Gate

Choose a common integral representative of the finite recursive carrier segment. Write the
current carrier as `(N,D)` and retain the preceding numerator in the exact denominator law

```text
D=EN₋.                                            (2)
```

For current and singleton-target upper/lower codes, write

```text
T₂=EP₂+GV₂,       T₃=EP₃+7G.                     (3)
```

The next-pole equation is

```text
(NT₂−10μGV₂D)T₃=EμG10^mN·7.                      (4)
```

Modulo `q`, equations (2)--(4) give

```text
q ∣ NG²V₂·7.                                      (5)
```

If the integral representative is gap-clean, meaning `gcd(q,N)=1`, then (1) cancels every
factor except the current lower code:

```text
V₂=qW.                                            (6)
```

This first gate alone is not a closure theorem. Compiler-emitted lower words can in principle
carry the gap factor.

## Quotient Gate

Substitute `E=9q`, `G=9g`, (2), (3), and (6) into (4). Cancelling the exact common factor
`81q` leaves

```text
[N(P₂+gW)−90μgqWN₋](qP₃+7g)=μg10^mN·7.           (7)
```

Reduction modulo `q` and the same coprimality cancellation now force

```text
q ∣ P₂+gW−μ10^m.                                  (8)
```

Equation (8) is not visible to the two/five-adic shell calculus saturated by `MM-S20`. It uses
both recursive denominator ancestry and the compiler's integral upper/lower trace form.

## Factorwise Ancestry

The complement of `gcd(q,N)=1` is shared-factor contamination, not `q∣N`. For example,
`2·10^5−7=43·4651`. Let `r` be any divisor of `q`. At a recursive multi-shell step, the
denominator law (2), the physical trace form, and the exact factorization

```text
NT−10μGVD=10^dN'
```

reduce modulo `r` to

```text
10^dN'≡NGV                                 (mod r).
```

Both `10` and `G` are coprime to every divisor of `q`, so

```text
r∣N'  ↔  r∣NV.                                    (9)
```

In particular, every prime `p∣q` satisfies `p∣N' ↔ p∣N or p∣V`. A gap prime can enter only
through a lower code and persists forever after entry.

The initial two-`c` raw head cannot contain the full gap. If its remaining `β` digits form
`fringe`, then

```text
27q < code(11·fringe) < 28q                       (β≥3).
```

Proper factors can divide this head, so prime support rather than full-gap divisibility is the
correct state.

Now factor `q=rs` with `gcd(r,N)=1`. Repeating the two cancellations above modulo `r` gives the
localized gates

```text
V₂=rW,
r ∣ s(P₂−μ10^m)+gW.                               (10)
```

Equation (10) recovers (6) and (8) at `r=q,s=1`, but remains active after unrelated factors of
`q` have entered the numerator.

## Gate Saturation

The factor gates are necessary, not sufficient. They already admit an all-`D_c` word at the
physical compiler width `β=10`. Put

```text
q = 19999999993,
d = 2483944320,
a = 15140917024,
k = 7511826864,
n = dk = 18658959671656212480.
```

Exact modular exponentiation gives

```text
10^d ≡ 1+9qa                              (mod 9q²),
70ak ≡ 34                                 (mod q).
```

For the word `D_c^n`, let `R_n=(10^n−1)/9`. Its current codes and upper length are

```text
V₂=7R_n,
P₂=5R_n10^(β+1)+μ,
m=n+β+1.
```

The first certificate gives `q∣R_n`; writing `V₂=qW`, it also gives `W≡7ak (mod q)`. The
physical identities `g+q=10μ`, `2·10^β≡7 (mod q)`, and `gcd(q,μ)=1` reduce the second full-gap
gate to

```text
10W≡34                                    (mod q),
```

which is exactly the second certificate. This is a computationally checked finite word in the
compiler alphabet, independent of the compiler body. It is not a false pole: it proves only
that the complete pair of gap congruences is satisfiable, so a closure needs carrier or suffix
semantics beyond them.

## Exact Boundary

The theorem removes every gap-clean carrier/current-code pair that fails either (6) or (8), at
every sign and length. It covers both singleton targets because their lower code is the same.
It does not classify which gap primes enter reachable carrier numerators, and it does not
exclude compiler-emitted pairs satisfying the quotient congruence.

The remaining physical multi-to-singleton seam is therefore the disjunction:

1. earlier lower words install some prime support of `q` into `N`; and
2. the current block passes (10) for every remaining numerator-coprime factor.

This is a strict reduction of the `m≥β+3` abstract carrier branch, not a proof of mortality
avoidance and not a false pole.

## Verification

`DecimalSetterAncestry.lean` proves the fixed coprimalities, raw-head interval, factor and prime
propagation laws, exact modular product reduction, factor cancellation, and both quotient
gates. The module is warning-free and uses no proof apertures. Its publication-facing theorems
are included in `AxiomAudit.lean`; the reviewed transitive axiom sets are recorded in
`verification/axioms.txt`. The all-`D_c` gate witness is computational evidence, not a Lean
theorem and not a reachability claim.

## Artifacts

- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s22-gap-factor-quotient-gate)
- [`MM-S24`](../SALVAGE.md#mm-s24-factorwise-gap-ancestry)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
