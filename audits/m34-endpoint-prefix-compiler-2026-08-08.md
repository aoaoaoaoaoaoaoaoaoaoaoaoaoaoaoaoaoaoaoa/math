# Endpoint-Prefix Compiler Audit

**Date:** 2026-08-08  
**Baseline:** `ec1b64a64e5569b69a1595a1592bc3739a49ba2b` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e23b-e2b4-83ea-92ed-32074c27505f

## Verdict

No three-pair GPCP reduction is obtained. The report does isolate an exact positive target: an
undecidable family of three-production prefix normal systems whose terminal equation forces every
intermediate rule application. Such a family compiles directly to `GPCP(3)`; no recurrent copy
letter is needed.

The negative result excludes every finite-phase certificate whose unmatched overlap has one
corrected drift sign under some positive target-symbol weighting. A universal three-schema source
must recurrently expand and contract in every positive Parikh direction and retain an unbounded
word-valued residual.

## Checked Direct Compiler

For productions

```text
αₓX ⟶ Xβₓ,
```

let a trace `w=x₁⋯xₖ` consume `A=αₓ₁⋯αₓₖ` and produce
`B=βₓ₁⋯βₓₖ`. Every lawful derivation from `s` to `t` satisfies

```text
sB = At.
```

`EndpointPrefixCompiler.lean` defines the execution relation and endpoint-prefix forcing. The
latter requires the terminal equation to imply, for every trace cut before `xⱼ`,

```text
Aⱼ is a prefix of sBⱼ₋₁.
```

Lean reconstructs the residual queue at every cut and proves the exact equivalence

```text
sB = At  ↔  the displayed trace lawfully derives t from s.
```

Setting `g(x)=βₓ`, `h(x)=αₓ`, and boundaries `(s,ε,ε,t)` is therefore a literal three-pair GPCP
compiler for every endpoint-prefix-forcing instance. The empty trace represents exactly the
zero-step derivation `s=t`.

The forcing hypothesis is essential. Lean checks a three-production system with source `0`,
target `ε`, and rule `01X⟶X1`: trace `a` satisfies `01=01` but cannot take its first step because
`01` is not a prefix of `0`. Injective target recoding preserves this false equality.

## One-Sided Drift Decision Boundary

For a finite controller, give each transition target words `(Uₑ,Vₑ)`, a positive symbol weight
`ω`, and a state potential `π`. Put

```text
κ(e)=|Uₑ|ω−|Vₑ|ω+π(source(e))−π(target(e)).
```

If every trim edge has `κ(e)≥0`, terminal weighted equality fixes the total sum of the `κ(e)`.
Every accepting prefix therefore spends between zero and that fixed budget. Prefix comparability
turns the weighted difference into the weight of the unmatched suffix, so all accepting
residuals have a computable length bound. Exact finite graph reachability decides existence. The
case `κ(e)≤0` follows after exchanging the sides.

For fixed `ω`, such a potential exists exactly when every trim cycle has nonnegative drift. The
existence of some positive rational `ω` and potential is a rational linear feasibility problem;
scaling gives integral weights. The same budget argument applies directly to finite-control
rewriting, since bounded intermediate weighted length leaves only finitely many configurations.
Lean checks the arithmetic throat `nonnegative_prefix_budget`; the potential construction,
residual graph, and decision procedure are independently audited rather than extracted as a Lean
algorithm.

For a one-state source, undecidability consequently requires, for every positive symbol weighting,
some recurrent production of negative drift and another of positive drift. Bounded delay,
equal-height tableaux, one-sided recurrent queue growth, and an acyclic cleanup phase are closed.

## Source Audit

Matiyasevich and Sénizergues prove undecidable accessibility for three-rule semi-Thue systems, but
their source rewrites arbitrary substrings. A rule-name trace omits every redex position and does
not determine the intervening contexts. Nicolas's locally retained construction pays two
recurrent copy symbols precisely to transport those contexts. The known theorem therefore does
not instantiate the direct prefix compiler.

The external report displays a proposed transcription of the Matiyasevich-Sénizergues rules and
suggests using their cancellation rule as an unbounded Dyck context channel. The primary paper is
not locally retained because no lawfully redistributable copy was found; its exact displayed
formulas and the strategic Dyck claim are not promoted. The theorem and the conventional `k+2`
compiler are supported through the retained Nicolas paper and the existing source sidecars.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Lawful prefix-normal traces satisfy the endpoint equation | promotion | Lean theorem `DerivesAlong.endpointEquation` |
| Endpoint prefix forcing makes the endpoint equation sufficient | promotion | Lean theorem `endpointEquation_iff_derivesAlong` |
| The unrestricted endpoint telescope admits underflow | promotion | Lean theorems `underflow_endpointEquation`, `underflow_not_derivesAlong` |
| One-sided corrected drift makes finite-phase certificate existence decidable | promotion | independently audited finite residual graph; Lean budget core |
| The displayed three-rule semi-Thue source compiles directly | rejected | arbitrary redex contexts are absent from the rule-name trace |
| An undecidable endpoint-prefix-forcing three-production family is known | rejected | no such family is supplied |
| `GPCP(3)` or `M₃(4)` follows | rejected | the required source family remains open |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every finite-phase three-schema certificate with one-sided corrected positive drift;
         the unrestricted normal-system endpoint telescope.
ADDED: a checked exact three-pair compiler for endpoint-prefix-forcing normal systems.
REMAINS: construct an undecidable three-production family with endpoint forcing, unbounded
         word-valued overlap, and recurrent drift of both signs in every positive direction.
```

## Artifact

- [`EndpointPrefixCompiler.lean`](../MatrixMortality/EndpointPrefixCompiler.lean)
