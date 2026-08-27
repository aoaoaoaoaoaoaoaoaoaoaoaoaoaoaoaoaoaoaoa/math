# Functional Phase-Transfer Audit

**Date:** 2026-08-11  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `8f51734fee83e455666d831d3e16789b0d307333` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3bea-934c-83ea-a4df-a415a73db43a

## Verdict

No universal three-production source and no `M₃(4)` reduction is obtained. The report does prove
a broad decidability theorem which kills the most natural head-separated queue architecture:
three positive chambers whose rule `i` transfers all net charge from its own chamber to one
definite different chamber.

The positive quotient arithmetic, complete three-vertex topology classification, explicit
one-sided weighting, cycle-product throat, and sharp mixed-drift counterexample are
kernel-checked. The final finite bounded-word reachability algorithm is independently audited.

## Positive Quotient

Let `dᵢ` be the Parikh displacement of production `i`. A positive phase-transfer quotient is a
nonnegative phase-by-symbol matrix `Q`, with positive support in every symbol column, satisfying

```text
Qdᵢ = −Aᵢeᵢ+Bᵢeτ(i),    Aᵢ,Bᵢ>0,    τ(i)≠i.
```

For positive phase weights `c`, the lifted symbol weight is

```text
ℓ(a) = Σᵥ cᵥQ(v,a).
```

Every `ℓ(a)` is strictly positive. Finite-sum rearrangement gives the exact rule drift

```text
ℓ·dᵢ = Bᵢcτ(i)−Aᵢcᵢ.
```

Lean proves both facts without treating the quotient as an informal change of coordinates:

- `FunctionalPhaseNoGo.liftWeight_pos`
- `FunctionalPhaseNoGo.symbolDrift_liftWeight_of_transfer`

## Functional Guillotine

A loopless map on three labeled phases has exactly eight forms: two directed three-cycles and
six two-cycles with one feeder. `FunctionalPhaseNoGo.exists_routeShape` proves this exhaustive
classification.

For every form, Lean constructs positive rational weights which make two edge drifts exactly
zero. For example, on `0→1→2→0`, take

```text
c₀=B₀B₁,    c₁=A₀B₁,    c₂=A₀A₁.
```

The first two drifts vanish. The third is either nonnegative or nonpositive, so all three have a
common weak sign. The other seven cases use the same spanning-tree construction. The combined
theorem is

```text
FunctionalPhaseNoGo.exists_positive_symbolWeight_oneSided.
```

The proof is stronger than an argument by logarithmic real weights: the certificate is rational,
explicit, and requires no optimization or feasibility oracle.

Lean separately proves the cycle-product necessity. Multiplying local drift inequalities around
a positive two- or three-cycle cancels all phase weights. Both sign orientations are checked by

- `twoCycle_product_le`, `twoCycle_product_ge`;
- `threeCycle_product_le`, `threeCycle_product_ge`.

## Decision Step

For a fixed source word `s` and target word `t`, one-sided positive symbol drift bounds every
intermediate successful word by one endpoint weight. Since the alphabet is finite and the
smallest symbol weight is positive, this gives a computable length bound. Enumerating the finite
word graph below that bound and performing graph reachability decides the instance.

This step uses no bounded-delay, regular-language, or finite-residue hypothesis. Arbitrarily long
balanced payload and arbitrary internal word order are allowed. The finite enumeration is
audited rather than reimplemented in Lean; no declaration is named as a generic decision
procedure.

## Sharp Fork

The functional hypothesis is essential. The three head-separated productions

```text
ppX ⟶ Xq,
pX  ⟶ Xqq,
qX  ⟶ Xp
```

have drifts, at positive symbol weights `(u,v)`,

```text
v−2u,    2v−u,    u−v.
```

For every `u,v>0`, one drift is strictly negative and another is strictly positive. Lean proves
the universal statement as `forkDrift_mixed` and its one-sided negation as
`forkDrift_not_oneSided`.

The phase graph is a forked two-cycle: two competing `P→Q` rules and one `Q→P` return. Its two
cycle products straddle one. This passes the necessary mixed-drift test but supplies no
universality theorem. It is a sharply delimited survivor, not a solution.

## Scope

The decidability theorem requires positive consumes, one source phase tied to each of the three
rules, one definite target phase per rule, and a nonnegative quotient whose every symbol column
has positive support. It does not cover:

- two rules drawing from the same phase, as in the fork;
- an empty-consume unconditional pump;
- net charge split among several future consumers;
- overlapping incomparable recurrent phase channels;
- a system with no such positive quotient.

The report's stronger arbitrary-finite-phase cycle-feasibility theorem is mathematically sound,
but the campaign needs only the complete three-rule throat. Lean therefore formalizes that exact
hot path rather than importing a general weighted-digraph library.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Positive quotient lifting preserves strict symbol positivity | formalized | `liftWeight_pos` |
| Lifted symbol drift equals weighted phase drift | formalized | `symbolDrift_liftWeight_of_transfer` |
| All loopless functional three-phase graphs have one-sided positive weights | formalized | `exists_routeShape`, `exists_positive_weight_oneSided` |
| Every functional positive quotient has one-sided symbol drift | formalized | `exists_positive_symbolWeight_oneSided` |
| Two- and three-cycle inequalities force product order | formalized | four `*Cycle_product_*` theorems |
| Fixed-endpoint reachability is decidable | audited | finite positive-weight sublevel graph |
| The fork has mixed drift under every positive weighting | formalized | `forkDrift_mixed` |
| The fork is undecidable or universal | rejected | no such proof was supplied |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every positive nonempty-consume functional private-head transporter on three schemas.
PRIMARY SURVIVOR: two competing P→Q schemas and one Q→P return, with straddling cycle products.
SECONDARY SURVIVORS: an empty-consume pump or genuinely nonfunctional phase splitting.
```
