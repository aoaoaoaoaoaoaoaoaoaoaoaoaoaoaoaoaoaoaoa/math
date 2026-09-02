# M₃(2) Casoratian and Order-Allocation Audit

Date: 2026-08-09

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

For a lawful first-hit terminal schedule `a₀,…,aₙ₋₁`, put `qᵢ=p^aᵢ`. The unresolved
split guard carried a radial terminal scalar `Xₙ` and the lower-left angular continuant `cₙ`.
The primitive terminal pole divides both by `gₙ=gcd(Xₙ,cₙ)`. The preceding frontier did not
locate `gₙ` inside the branch history and therefore could not distinguish new final
cancellation from recycled earlier support.

The exact terminal Casoratian removes the final branch from this gcd. Two complementary
prime-power inductions then consume every exact-order factor whose order persists to either
chronological boundary. The remaining split-guard obstruction is the doubly order-broken
residue, not arbitrary additive prime creation.

## Terminal Casoratian

Let `P` be the endpoint product before the final transfer `T(q)`, let `v=(R,1)ᵀ`, and write

```text
Pv=(u,z)ᵀ,   c⁻=P₂₁,
T(q)P v=(0,X)ᵀ,   c=(T(q)P)₂₁.
```

The lower row of every endpoint transfer is `(1,−L(q−1))`. Hence

```text
z c − X c⁻
= z(P₁₁−L(q−1)P₂₁)
  − ((u−L(q−1)z)P₂₁)
= zP₁₁−uP₂₁
= det P.
```

The last equality uses `u=RP₁₁+P₁₂` and `z=RP₂₁+P₂₂`. Therefore every
common divisor of `X` and `c` divides `det P`, exactly the determinant support before the final
branch. Lean proves the stronger transfer identity without assuming terminality and then the
terminal divisor corollary:

```text
ReturnGuard.endpointTransfer_casoratian
ReturnGuard.terminalCommonDivisor_dvd_previousDet
```

Since

```text
det P=(−1)^(n−1) p^(s∑ᵢ<n−1 aᵢ)
      ∏ᵢ<n−1 DL(qᵢ−1)
```

and the checked mod-`p` endpoint flag makes `cₙ` a `p`-unit, this gives

```text
gₙ ∣ (DL)^(n−1) ∏ᵢ<n−1(qᵢ−1).
```

No factor from the final boundary can first enter primitive normalization.

## Two-Sided Exact Orders

Let `hᵢkᵢ=DL(qᵢ−1)` be the signed forward/reverse content split and set

```text
eᵢ=gcd(a₀,…,aᵢ),   dᵢ=gcd(aᵢ,…,aₙ₋₁),   Δ=DLR.
```

For `m≥1`, let `Πₘ(p)` retain, with full multiplicity, the factors of `Φₘ(p)` whose
prime does not divide `m`; these primes have exact order `m`. Let `Πₘ^(Δ)` delete exactly
the prime support of `Δ`. Then every terminal primitive execution satisfies

```text
Π_(dᵢ)^(Δ) ∣ hᵢ,   Π_(eᵢ)^(Δ) ∣ kᵢ.
```

For the forward law, a missing prime power in `hᵢ` lies in `kᵢ`. Its order divides every
later wait, so it recurs at every later boundary. The checked
`PrimitiveEndpointReduction.recurrentBoundaryDivisor_persists` theorem keeps it in reverse
content through the final step, contradicting `kₙ₋₁ ∣ LR`.

For the reverse law, a missing prime power in `kᵢ` lies in `hᵢ`, hence divides the current
endpoint numerator. If it failed to divide the preceding forward content, the complementary
reverse content and the checked reset-defect divisor would force the primitive denominator to
vanish modulo that prime while the reset-defect numerator and denominator remain units. Induction
reaches `h₀ ∣ DR`, contradicting removal of the `DLR` support.

Both arguments retain prime-power multiplicity. Neither assumes monotone waits.

## Effective Consequences

The checked primitive-part inequality gives, for `m>2`,

```text
(p−1)^φ(m) ≤ m Πₘ(p).
```

LTE bounds the portion supported on the fixed primes of `Δ` by `CΔ m^r`. Together with
`φ(m)²≥m/2`, this computes a threshold `A₀` such that

```text
Πₘ^(Δ)>C₀  whenever m≥A₀,
```

where `|hᵢ|Hᵢ₊₁≤C₀Hᵢ` is the direct primitive endpoint-height inequality. At
`i=0`, the suffix order is the gcd of all waits and `h₀∣DR`, so every terminal schedule has
global wait gcd in the finite computable set

```text
{m<A₀ : Πₘ^(Δ)=1}.
```

If `a₀∣a₁∣⋯∣aₙ₋₁`, then every suffix gcd equals its first member. Below `A₀`,
exact common-branch similarity bounds each fixed-wait run unless it is a nonterminal fixed
point; every strict divisible increase at least doubles the wait. At and above `A₀`, the
positive integer height decreases strictly at each continuing chain step. Exact simulation
therefore decides this entire deterministic stratum.

The decreasing lawful word `[3,1]` is not covered: both suffix gcds equal one, while the
order-three factor at the first step is assigned backward. It is the minimal checked witness to
the surviving order-breaking mechanism.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| terminal common divisors lie in pre-final determinant support | formalized | exact lower-row determinant identity |
| `gₙ` has no distinguished-prime factor | already formalized | follows from the fixed mod-`p` endpoint flag |
| prefix/suffix exact-order allocation | promotion | independently reconstructed with full multiplicity |
| global wait gcd belongs to an effective finite set | promotion | primitive-part growth plus the initial boundary |
| divisibility-chain terminal schedules are decidable | promotion | finite fixed-wait blocks followed by strict height descent |
| the complete split guard is decided | rejected | arbitrary doubly order-broken schedules remain |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: fresh final-branch normalization; exact-order mass persisting to either boundary; all divisibility-chain terminal schedules
REMAINS: doubly order-broken schedules in which earlier reverse content repeatedly finances later angular cancellation
NEXT DECISION CUT: amortize every order-breaking bridge, or construct one reset-started aperiodic prime genealogy satisfying the exact content ledger indefinitely
```
