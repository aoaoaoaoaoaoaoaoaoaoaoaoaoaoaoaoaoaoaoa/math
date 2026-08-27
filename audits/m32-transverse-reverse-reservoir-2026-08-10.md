# M₃(2) Transverse Reverse-Reservoir Audit

Date: 2026-08-10

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The split-guard decision lane sought a potential charging every forward and reverse allocation
of the cyclotomic factors `pᵃ−1`. If such a charge were controlled by the coefficients and the
projective endpoints, a first-hit terminal execution might admit a computable length bound.

The submitted global estimates are valid but do not bound length. More decisively, the checked
period-three guard stores an arbitrary 13-power in the endpoint macro's transverse eigenvalue
while its lawful rational orbit remains fixed. Endpoint-only reverse-mass coercivity is false.

## Global Reset-Defect Budget

Use an integral presentation

```text
C=A/L,    δ=D/L,    R=A+D−L,
```

and a primitive endpoint execution `vᵢ=(rᵢ,tᵢ)`, with signed forward content `hᵢ`, wait power
`qᵢ=p^aⁱ`, and `Hᵢ=max(|rᵢ|,|tᵢ|)`. The checked primitive equations are

```text
qᵢˢ hᵢ tᵢ₊₁ = rᵢ−L(qᵢ−1)tᵢ,
hᵢ rᵢ₊₁    = D rᵢ+(A−L)hᵢtᵢ₊₁.
```

Put

```text
C*=max(1+|L|, |D|+|A−L|(1+|L|)),
K*=1+|R|,    Δᵢ=rᵢ−Rtᵢ.
```

Direct elimination gives

```text
|hᵢ|Hᵢ₊₁ ≤ C*Hᵢ,
hᵢΔᵢ₊₁ = D(qᵢ−1)(Ltᵢ+(1+qᵢ+⋯+qᵢˢ⁻¹)hᵢtᵢ₊₁).
```

Hence `qᵢ−1 ∣ hᵢΔᵢ₊₁`. On a reset-avoiding prefix of length `n`,

```text
Hᵢ ≤ C*ⁱH₀,
∏ᵢ<n(qᵢ−1) ≤ K*ⁿ C*^(n(n+1)/2) H₀ⁿ.
```

For a first-hit terminal schedule, every proper prefix avoids reset by determinism. The total
wait mass is therefore coefficient-effectively `O(n²)`, but this is compatible with unbounded
`n`. At the terminal pair, telescoping also gives

```text
∏ᵢ<n|hᵢ| ≤ C*ⁿH₀.
```

The endpoint product is rank one modulo `p`, with lower-left coefficient a `p`-unit. Combining
this with the terminal scalar factorization bounds the scalar/coefficient gcd by the same
forward-content product. These are valid audited corollaries of the checked `R32-S29` content
calculus; a second formal recurrence API would duplicate its owner.

Every nonempty endpoint macro is also p-adically hyperbolic: its trace is a p-unit while its
determinant has positive valuation `s∑aᵢ`. Its Newton slopes are therefore `0` and `s∑aᵢ`.
Projectivization retains one eigenline and discards the scalar on the other.

## Exact Transverse Reservoir

For the checked guard

```text
(p,s,A,D,L)=(3,2,−953,473,2240),    R=−2720,
```

the primitive endpoint cycle is

```text
(−2720,1) --1,h=−160--> (−7924,5)
          --2,h=−1204--> (−80,1)
          --3,h=−80-->   (−2720,1).
```

The complementary reverse contents `kᵢ=DL(3^aⁱ−1)/hᵢ` are

```text
k₀=−13244,    k₁=−7040,    k₂=−344344.
```

Three has order three modulo thirteen, which divides only `k₂` and none of the forward
contents. Let `M` be the endpoint product for `[1,2,3]`. Lean checks the two rational eigenlines

```text
M(−2720,1)ᵀ        = −8190143539200 (−2720,1)ᵀ,
M(193981136,5587)ᵀ = 32105863229440 (193981136,5587)ᵀ,
```

where

```text
−8190143539200 = 3¹²(−160)(−1204)(−80),
32105863229440 = (−1)³(−13244)(−7040)(−344344)
               = 13·2469681786880,
gcd(13,2469681786880)=gcd(13,−8190143539200)=1.
```

For every `N`, `repeatSchedule [1,2,3] N` is lawful from residual reset and returns exactly to
reset. Its endpoint product acts by the `N`th powers of the displayed eigenvalues. The reverse
eigenvalue therefore has exact 13-adic valuation `N`, while the visible reset eigenvalue remains
13-adically unit. This is formalized by
`ReturnGuard.Examples.cycle_transverseReservoir`; the three primitive reductions and determinant
splits are checked by `cycle_endpointReductions` in
[`ReturnGuardTransverseReservoir.lean`](../MatrixMortality/ReturnGuardTransverseReservoir.lean).

The counterfamily is immortal rather than terminal. It refutes path-independent or
endpoint-coercive reverse-mass potentials, not a theorem using first-hit terminality,
reset anchoring, and aperiodicity.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| full-multiplicity reset-defect and branch-mass bounds | promotion | valid audited corollaries of `R32-S29`; quadratic in path length |
| terminal forward-content and scalar/coefficient gcd bounds | promotion | valid, but still exponential in path length |
| every nonempty macro is p-adically hyperbolic | salvage | valid Newton-polygon consequence; it supplies no escape certificate |
| all reverse packets can be charged from coefficients and endpoints | rejected | the exact repeated period-three reservoir has fixed projective orbit and unbounded transverse 13-mass |
| fixed-bridge resultant bounds decide the orbit | rejected | degree and height grow with the unknown bridge; vanishing resultants return to projective incidence |
| fixed-support S-unit bounds decide the orbit | rejected | the number of summands and cyclotomic support are not fixed |
| a reset-anchored terminal bound follows | open | the counterfamily is periodic and nonterminal |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
KILLED: every path-independent projective-endpoint potential charging all reverse cyclotomic mass
SHARPENED: total waits and all forward/reactivated mass have coefficient-effective bounds in the unknown length
REMAINS: effective recurrence-or-escape for a reset-started aperiodic unbounded-denominator orbit, or one exact construction
```
