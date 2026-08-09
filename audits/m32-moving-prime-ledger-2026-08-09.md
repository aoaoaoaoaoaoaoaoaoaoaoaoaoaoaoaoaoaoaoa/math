# M₃(2) Moving-Prime Ledger Audit

Date: 2026-08-09

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The opposing split-guard route requires one reset-started aperiodic orbit whose primitive
normalizations use continually changing factors of `pᵃ−1`. The missing local question was whether
such a factor could enter forward content through hidden cancellation not visible in the
current endpoint state.

It cannot. Away from the fixed `pDL` support, forward allocation is exactly simultaneous
divisibility of the current endpoint numerator and the current branch boundary. This closes the
local ledger but neither constructs nor excludes an infinite genealogy.

## Exact Ledger

For one primitive endpoint reduction, write

```text
p^(sa) h t⁺ = r−L(pᵃ−1)t,
h r⁺ = Dr+(A−L)h t⁺,
h k = DL(pᵃ−1).
```

Let `d` be any integer with `gcd(d,pDL)=1`. Then

```text
d ∣ h  ⇔  d ∣ r  and  d ∣ pᵃ−1.                    (∗)
```

The forward implication uses `h∣Dr` and `h∣DL(pᵃ−1)`. For the converse, simultaneous
divisibility makes both raw target coordinates divisible by `d`; coprimality with the base power
removes `p^(sa)`, and primitivity of `(r⁺,t⁺)` forces `d∣h`. Lean checks this argument for an
arbitrary composite divisor, hence for every prime power at once:

```text
ReturnGuard.PrimitiveEndpointReduction.divisor_dvd_content_iff
```

For a prime `ℓ∤pDL`, (∗) is equivalent to

```text
vℓ(h)=min(vℓ(r),vℓ(pᵃ−1)),
vℓ(k)=max(0,vℓ(pᵃ−1)−vℓ(r)).
```

The equal-valuation case permits extra cancellation in the prequotient but cannot raise the
content above the valuation already present in `r`; this is exactly why the divisor form is
stronger and cleaner than a case split.

## Casoratian Synthesis

The report's angular Wronskian is the terminal Casoratian already promoted in `R32-S33`, after
dividing cumulative forward content. Its delayed-activation consequence is valid. If a prime
`ℓ` divides an angular continuant coefficient but no earlier coefficient or branch determinant
support, the Casoratian makes it coprime to the current primitive denominator. It becomes
available for content only at a later wait satisfying

```text
ord_ℓ(p) ∣ aⱼ,
```

and (∗) then additionally requires `ℓ` in the current endpoint numerator. Additive creation
alone is sterile; useful memory requires later order synchronization and state coincidence.

## Culled Restatements

The reciprocal coordinate `y=Lt/r` rewrites the same cumulative endpoint step as

```text
β=(pᵃ−1)α+p^(sa)c,
(α⁺,β⁺)=primitive(Lc,Dβ+(A−L)c).
```

It removes no state or obstruction and is not retained as a second recurrence API.

The proposed no-Mahler theorem is also already checked in stronger form. The existing rational
rail equation uses substitution `X↦λXᵏ`; `ReturnGuard.Rail.not_identity_of_degreeGrowth`
excludes every degree `k>1` before the later affine-rail specialization. No new rational-function
theorem is needed.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| exact reciprocal Euclidean recurrence | restatement | coordinate rewrite of cumulative endpoint reduction |
| prime-power moving-content ledger | formalized | divisor equivalence (∗) for arbitrary composite `d` |
| angular Wronskian | restatement | same determinant identity as `R32-S33` |
| emergent primes require later order synchronization | promotion | exact consequence of Casoratian plus (∗) |
| no rational Mahler rail `a⁺=ka+d`, `k≥2` | already formalized | subsumed by `Rail.not_identity_of_degreeGrowth` |
| an infinite moving-support orbit exists | open | no reset-started execution was produced |
| every moving-support orbit terminates or repeats | open | no global height theorem was proved |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: hidden auxiliary-prime allocation; additive prime names as self-activating memory; rational one-chart Mahler rails as a new lane
REMAINS: an aperiodic sequence of synchronized prime births satisfying the exact ledger while sustaining unbounded reduced denominators
DECISION DUAL: prove that every such genealogy exhausts its two-sided order budget
```
