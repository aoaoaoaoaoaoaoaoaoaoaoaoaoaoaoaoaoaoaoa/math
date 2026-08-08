# M₃(2) Finite Radial-Atlas Obstruction Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

After fixed-prime counter charts failed, a weaker construction remained conceivable: finitely
many rational angular modes `T_v(p^a)` could switch among finitely many bridge types, each
changing the wait by a fixed additive amount. Such an atlas could in principle hide aperiodicity
in its control graph without admitting one global affine rail.

It cannot. Every directed atlas cycle has total wait shift zero, and every actual infinite orbit
in the class is eventually periodic. A surviving counter-orbit must use infinitely many charts,
infinitely many wait differences, or angular history not rationally determined by the current
radial coordinate and one finite mode.

## Exact Atlas

For a ready state at wait `a`, write `X=p^a` and

```text
z=X+X^s/T_v(X),   T_v=P_v/Q_v ∈ ℚ(X),
```

with `P_v,Q_v` reduced and nonzero at zero. An edge `e:v→w` has fixed integer shift `d_e`,
`λ_e=p^(d_e)`, and is required to satisfy the exact tail identity

```text
C+δ(X^s+(X−1)P_v(X)/Q_v(X))
  =λ_eX+(λ_eX)^s Q_w(λ_eX)/P_w(λ_eX).
```

The nonzero constant-term condition is automatic for any reduced chart sampled as a p-adic unit
at unbounded waits.

## Cycle Rigidity

For one edge, abbreviate `P=P_v`, `Q=Q_v`, `P̂=P_w(λX)`, and `Q̂=Q_w(λX)`. Clearing
denominators and reducing modulo `P̂` gives `P̂ ∣ Q`, because `P̂` is coprime to both `X`
and `Q̂`. Write

```text
Q=P̂H.
```

After cancellation, coprimality of `P,Q` forces `H ∣ X−1`; hence `deg H=ε_e∈{0,1}`.
If `n_v=deg P_v`, `m_v=deg Q_v`, and `k_v=n_v−m_v`, exact degree transport is

```text
m_v=n_w+ε_e.
```

Around a cycle, `Σk_v=−Σε_e≤0`, so some source has `k_v≤0`. Comparing degree at
infinity in the tail identity forces its target to have `k_w=0`; propagation around the cycle
forces every `k_v=0` and every `ε_e=0`. All numerator and denominator degrees on the cycle
therefore have one common value `N`, and

```text
Q_v(X)=κ_e P_w(λ_eX).
```

Evaluation at zero gives

```text
C^ℓ ∏κ_e=δ^ℓ.
```

Cancellation of the potential leading terms of degree `N+s` gives

```text
δ^ℓ=(∏κ_e)(∏λ_e)^(N+s).
```

Consequently

```text
C^ℓ=(∏λ_e)^(N+s).
```

The normalized center `C` is a p-unit and `N+s>0`, so p-adic valuation forces

```text
Σ_e d_e=0
```

on every directed cycle.

## Orbit Consequence

An edge used infinitely often by a nonperiodic actual orbit is sampled at infinitely many
distinct `p^a`; otherwise one chart and radial coordinate repeat the same rational state, and
determinism makes the future periodic. Its cleared transition defect therefore has infinitely
many roots and is the rational identity above.

After finitely occurring transitions are discarded, every cycle in the recurrent finite graph
has weight zero. The edge weights are a coboundary `d_e=h(w)−h(v)`, so

```text
a_n−h(v_n)
```

is constant. Only finitely many waits and chart states remain. One state repeats and the orbit
is exactly eventually periodic; its primitive reduced denominators are bounded.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| edge divisibility `P_w(λX) ∣ Q_v(X)` | promotion | direct coprime reduction after clearing denominators |
| quotient divides `X−1` | promotion | follows from reduced source chart |
| every atlas cycle has zero total shift | promotion | degree, constant-term, leading-term, and p-adic valuation argument independently reconstructed |
| every actual finite-atlas orbit is eventually periodic | promotion | recurrent-edge identity plus graph coboundary and determinism |
| every guard orbit admits such an atlas | rejected | the class explicitly forgets unbounded angular history |
| no aperiodic reset orbit exists | open | it may require an infinite atlas or unbounded transition alphabet |

No Lean rational-function atlas was retained. Its only consumer is the audited impossibility
statement, while the exact single-chart rail and bounded-denominator periodicity already own the
executable local and orbit boundaries. Formalizing another atlas ontology would not narrow the
remaining master enemy.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: every finite rational carry-mode atlas with fixed additive wait shifts; finite-state radial rational counter-orbits
REMAINS: genuinely history-sensitive moving cyclotomic support, infinitely many effective charts or shifts, or a coefficient-effective continuant bound
DISTANCE: any aperiodic witness must remember unbounded angular information not recoverable from p^a and finite control
```
