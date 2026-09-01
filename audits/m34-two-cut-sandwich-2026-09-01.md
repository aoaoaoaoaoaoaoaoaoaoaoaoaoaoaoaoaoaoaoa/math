# M₃(4) Two-Cut Sandwich Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `51aac54` on `wave3-m34-transverse`
**Formal artifact:**
[`MixedPrimeAddressSandwich.lean`](../MatrixMortality/MixedPrimeAddressSandwich.lean)

## Verdict

Uniform double insertion does not create diffuse comparator geometry. Five finite address probes
force its three fixed context pairs to have equal affine actions. For a prefix-kernel-free
relation the two cuts align and reduce to the endpoint placements `(0,0)`, `(N,N)`, or the central
sandwich `(0,N)`. The central placement is a positive result: every genuine affine kernel pair
gives an exact raw-distinct comparator for addresses of arbitrary, unequal initial lengths.

## Five-Probe Collapse

Write the affine data of the three contexts as `(p,p₀)`, `(q,q₀)`, `(r,r₀)`. For an address with
multiplier `μ=(2/5)^|a|` and offset `ξ`, Lean proves

```text
slope(P W Q W R)=p μ² q r,
offset(P W Q W R)=p₀+pμq₀+pμ²qr₀+p(1+μq)ξ.
```

Subtracting the `[0]/[1]` equations at depths one and two isolates `p(1+μq)` at the distinct
values `2/5` and `4/25`. This recovers `p` and `q`; the complete slope recovers `r`. The empty,
depth-one, and depth-two offset equations form a nonsingular quadratic interpolation system and
recover `p₀,q₀,r₀`. The formal theorem accepts exactly the five probes; the uniform theorem is a
corollary.

## Exact Sandwich

If `L` and `R` have one affine action, then

```text
action(Wᵤ L Wᵤ)=action(Wᵥ R Wᵥ)  iff  u=v.
```

Equality of composite slopes recovers address length. After the kernel action is substituted,
evaluation at zero leaves `(1+μ·scale(R))(offset(u)−offset(v))=0`. The coefficient is positive,
and the macro-address offset is globally injective. If `L≠R`, raw equality would first force
`u=v` and then cancel both address copies to force `L=R`; hence every pair of sandwich words is
raw-distinct.

## Physical Sieve

For the literal reduced fork

```text
yzxyx = W L W,
xzyxy = W R W,
```

noncommutation `xy≠yx` forces `|W|<|x|+|y|`: otherwise both `yx` and `xy` are equal-length
suffixes of the common suffix `W`. The exact length equation then gives `|toggle|<|L|`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Five probes force all three context pairs into the affine kernel | promoted | Lean theorem |
| Arbitrary uniform double insertion has additional algebraic freedom | rejected | five-probe corollary |
| Prefix-kernel-free relations admit distributed internal cuts | rejected | formal cut trichotomy |
| The central sandwich is an exact address comparator | promoted | Lean theorem, no equal-length premise |
| The sandwich raw words can collapse despite `L≠R` | rejected | formal two-sided cancellation |
| Every listed pump relation physically realizes the sandwich | open | boundary catalogue not yet composed |
| The arbitrary-word terminal converse follows | open | outside affine comparison |
| `M₃(4)` follows | rejected | physical realization and converse remain |

## Master Delta

```text
DEAD: diffuse uniform two-cut placement.
LIVE: one exact central sandwich W·L·W/W·R·W.
GATE: literal bcbc factorization with |W|<|x|+|y| and |toggle|<|L|.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, Lean LSP
diagnostics, forbidden-aperture scan, and source scour pass.
