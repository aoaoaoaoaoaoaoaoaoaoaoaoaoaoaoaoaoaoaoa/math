# Decimal Setter Arithmetic Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the decimal setter has an exact centered carry, two coupled `2`/`5` target
shells, and a reciprocal recurrence; the surviving shell preserves both the valuation gap and
the first normalized decimal unit

Nothing below proves arbitrary-depth pole avoidance or `M₅(3)`.

## Integral Carry

Retain the radix-ten parameters of the decimal setter. Put

```text
ρ=10^β,                    9μ+7=52ρ,
E=9(2ρ−7),                 G=502ρ−7,
P=μ+10ρU,                  A=10^m,
T=EP+GV.
```

Thus `G/E` is the projective shift `L`. If `t=X/Y`, one J-fraction step has the exact
homogeneous lift

```text
X′=TX−GVY,
Y′=EμAX.                                             (1)
```

Write `Δ=Y−X`. Equation (1) becomes

```text
X′=EPX−GVΔ,
Δ′=E(μA−P)X+GVΔ,
X′+Δ′=EμAX.                                         (2)
```

The centered coordinate

```text
Z=(G/E)Δ/X
```

therefore obeys

```text
Z′=(G/E)(μA−P+VZ)/(P−VZ).                           (3)
```

The ordinary reset is `Z=0`. Since `G+E=90μ`, the distinguished reset is represented by
`(X,Δ)=(G,E)` and has `Z=1`. Its pole equation is

```text
EPG−GVE=EG(P−V)=0,
```

so it is a pole exactly when `P=V`, the genuine terminal match.

The reciprocal coordinate

```text
W=GY/X=EZ+G
```

is still simpler:

```text
W′=EGμ10^m/(T−VW),               pole ⇔ W=T/V.       (4)
```

Its resets are `G` and `G+E=90μ`. Equation (4) exposes the trace `T` as the sole arithmetic
target and removes the apparent Möbius asymmetry.

These identities are formalized in
[`DecimalSetterArithmetic.lean`](../MatrixMortality/DecimalSetterArithmetic.lean), through
`nextNumerator_centered`, `nextDefect_centered`, `centeredCoordinate_step`,
`reciprocalCoordinate_step`, and `distinguished_pole_iff`.

## Exact Trace Shells

All of `E`, `G`, `μ`, `P`, and every nonempty lower code `V` are units at both `2` and `5`.
The final decimal digits classify `T`.

### Multi-role erasure target

Every admissible pole block ends in an erasure. If at least one role precedes it, then

```text
ρ≡0,       E≡37,       G≡93,       P≡77,       V≡77   (mod 100).
```

Consequently

```text
T≡10 (mod 100),                  (ν₂(T),ν₅(T))=(1,1).  (A)
```

Only the two final digits are needed. A previous scratch claim used `V≡177 (mod 200)`.
That claim fails for two singleton erasures, whose lower code is `77`; the corrected
modulo-`100` statement proves the same shell without an exception.

### Single erasure target

For `D_c`, direct simplification gives

```text
T_Dc=2ρ(502ρ−7).
```

For `D_b`, the long upper code gives

```text
T_Db=2ρ(5200ρ²−18398ρ+2443).
```

Both cofactors end in `3`. Hence

```text
(ν₂(T_Dc),ν₅(T_Dc))=(ν₂(T_Db),ν₅(T_Db))=(β+1,β).     (B)
```

Lean proves both classifications as `multiErasure_trace_hasDecimalShell`,
`singleCErasure_trace_hasDecimalShell`, and `singleBErasure_trace_hasDecimalShell`.

A regular block between delimiter squares always ends in an erasure. Rule-ending fragments are
incomplete exterior factors; invertibility already excludes them from mortality. They are not
transitions in the carry system.

## Successive-pole Law

Suppose `(X₁,Δ₁)` is the output of a block of upper length `m`, and the next block is a pole.
Combining its pole equation with `X₁+Δ₁=Eμ10^mX₀` gives the exact identity

```text
T_target X₁=EGμV_target 10^m X₀.                     (5)
```

Since the four coefficients outside `T_target` are decimal units, (5) forces, for
`p∈{2,5}`,

```text
ν_p(T_target)+ν_p(X₁)=m+ν_p(X₀).                     (6)
```

In particular, if `d(X)=ν₅(X)−ν₂(X)`, then

```text
d(X₁)−d(X₀)=ν₂(T_target)−ν₅(T_target).               (7)
```

Thus shell A preserves `d`, while shell B raises it by one. Lean checks (5)–(7) in
`successive_pole_identity`, `successive_pole_shellBalance`, and
`successive_pole_gapShift`.

## Surviving Corridor

Shell A is the live arbitrary-depth obstruction. It preserves the joint valuation gap. It also
preserves the first dangerous decimal unit: from `T/10≡1` and `V≡7 (mod 10)`,

```text
(T/V)/10≡3 (mod 10).
```

The distinguished reset satisfies `(90μ)/10=9μ≡3 (mod 10)`. Therefore neither the pair of
valuations nor its first normalized unit separates the reset from a false multi-role pole.
This explains the rapid saturation of the earlier gap and residue searches.

Exact bounded enumeration for the body `bcbbbbbbc` found no pole through four transfers when
each role block has length at most two. A separate exact meet-in-the-middle search on the
strongly elliptic high/low pair found no pole through thirty-six transfers. These are finite
falsification results, not theorem evidence.

The next certificate must retain the normalized decimal suffix across repeated A-shell
resonances. The minimal useful experiment is backward symbolic saturation from `W=T/V`, with
states consisting of the clipped valuation pair and the unreduced normalized suffix of
`T−VW`. Any quotient that forgets that suffix has already re-entered the target shells by
depth two.
