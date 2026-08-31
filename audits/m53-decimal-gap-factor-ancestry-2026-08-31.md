# Decimal Setter Gap-Factor Ancestry Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the raw-head gap-prime support and its lower-code ancestry are exact, and every
still-clean factor imposes two singleton congruences; those congruences are jointly attainable
by a physical all-deletion word and do not close the setter

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

## Initial Support

The unit two-`c` raw-head grammar supplies a terminal run length `s`, with `1≤s≤β−1`, and the
exact identity

```text
9H=5·10^(β+2)+2·10^s−7
  =250q+(2·10^s+1743).                            (11)
```

Every `r∣q` is coprime to nine: equation (1) gives `gcd(q,G)=1`, while `9∣G`, and coprimality
descends to divisors. Reducing (11) modulo `r` and cancelling nine therefore gives

```text
r∣H  ↔  r∣2·10^s+1743.                           (12)
```

Equation (12) classifies the complete initial gap-prime support by one run-length exponential.
Together with (9), it separates support already present at the raw head from support first
installed by a later compiler-emitted lower code.

Put `t=β−s`. The identity

```text
10^t(2·10^s+1743)=q+7(249·10^t+1)                (13)
```

and the automatic coprimalities `gcd(r,7)=gcd(r,10)=1` give the reciprocal form

```text
r∣H  ↔  r∣249·10^(β−s)+1.                        (14)
```

This support is exactly periodic. Once `r∣249·10^t+1`,

```text
r∣249·10^(t+k)+1  ↔  r∣10^k−1.                  (15)
```

Once `r∣q(β)`, the same right side characterizes `r∣q(β+k)`. These are integral equivalences,
not an appeal to an unformalized discrete logarithm.

Proper-factor entry occurs in the physical raw grammar. At `β=5`, the role word `cccccb` has
peeled head `1111110`, so

```text
q=199993=43·4651,
H=5555557=43·129199.                              (16)
```

Equation (16) refutes a universal gap-clean initial-carrier invariant. Moreover
the multiplicative order of ten modulo `43` is exactly `21`, so the exact shift laws give

```text
43∣q(5+k) and 43∣249·10^(4+k)+1  ↔  21∣k.         (17)
```

Thus terminal-run-one support occurs exactly at widths congruent to five modulo `21`. This is
an infinite arithmetic family of support entries, not a false pole.

## Gcd-Saturated Gate

The factorwise gate can be made canonical without any coprimality branch. Put

```text
c=gcd(q,N),       r=q/c,       N₀=N/c.
```

Because `q≠0`, the gcd is nonzero, and exact Euclidean division gives

```text
q=rc,       N=cN₀,       gcd(r,N₀)=1.             (18)
```

The first pole reduction now says

```text
cr ∣ cN₀G²V₂·7.
```

Cancel `c`, then cancel `N₀G²·7`, which is coprime to `r`. Thus `V₂=rW`. Substitution into
the exact pole equation exposes a common factor `81cr`; cancelling it and reducing modulo `r`
gives

```text
r ∣ c(P₂−μ10^m)+gW.                               (19)
```

Equations (18)--(19) leave no gcd or coprimality side condition. Partial prime-power support is
accounted for by the quotient `q/gcd(q,N)`. The modulus is a unit only when the complete gap
already divides the carrier numerator.

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
Equations (12)--(15) exactly classify support in the initial unit raw head and its width shifts;
(16)--(17) show that proper support occurs infinitely often. Equation (19) retains the strongest
quotient gate for every partial contamination pattern. These results do not classify support
installed by later lower codes, prevent full-gap contamination, or exclude compiler-emitted
pairs satisfying the canonical quotient congruence.

The remaining physical multi-to-singleton seam is therefore the disjunction:

1. earlier lower words install the complete gap `q` into `N`; or
2. the current block passes (19) modulo the canonical quotient `q/gcd(q,N)`.

This is a strict reduction of the `m≥β+3` abstract carrier branch, not a proof of mortality
avoidance and not a false pole.

## Verification

`DecimalSetterAncestry.lean` proves the fixed coprimalities, exact raw-head support, factor and
prime propagation laws, exact modular product reduction, common-factor cancellation, and the
factorwise and gcd-saturated quotient gates. The module is warning-free and uses no proof
apertures. Its publication-facing theorems are included in `AxiomAudit.lean`; the reviewed
transitive axiom sets are recorded in `verification/axioms.txt`. The all-`D_c` gate witness is
computational evidence, not a Lean theorem and not a reachability claim.

## Artifacts

- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s22-gap-factor-quotient-gate)
- [`MM-S24`](../SALVAGE.md#mm-s24-factorwise-gap-ancestry)
- [`MM-S26`](../SALVAGE.md#mm-s26-exact-raw-head-prime-support)
- [`MM-S27`](../SALVAGE.md#mm-s27-reciprocal-raw-head-support)
- [`MM-S31`](../SALVAGE.md#mm-s31-gcd-saturated-singleton-gate)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
