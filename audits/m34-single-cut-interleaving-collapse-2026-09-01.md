# M₃(4) Single-Cut Address-Interleaving Collapse Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `3b56aa3` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeAddressInterleavingCollapse.lean`](../MatrixMortality/MixedPrimeAddressInterleavingCollapse.lean)

## Verdict

Inserting the free `{DT,TD}` address at one fixed cut of a kernel cloak does not create a new
uniform comparator geometry. Suppose fixed words `P,Q,R,S` satisfy

```text
P·expandAddress(u)·Q  =  R·expandAddress(u)·S
```

as affine actions for every address `u`. The empty address and the two one-digit probes `DT,TD`
already force

```text
action(P)=action(R),       action(Q)=action(S).
```

Thus the interleaving splits into independent equal-action pairs before and after the address.
If the complete same-address words are raw-distinct, at least one side is itself a genuine kernel
pair. Lean composes this with exact `bcbc` endpoint semantics: every uniform single-cut physical
fork contains a genuine kernel pair wholly on one side of the cut.

## Three-Probe Proof

The `DT` and `TD` address macros have one multiplier `2/5` and distinct offsets `2/3` and `1`.
Subtracting their two interleaved action equations cancels both suffix values and proves that
`P,R` have equal slopes. Subtracting the empty-address equation from the `DT` equation then gives

```text
scale(P)·(2/5-1)·(action(Q)(x)-action(S)(x))=0.
```

Every mixed-prime word has positive slope, so `action(Q)=action(S)`. Surjectivity of `action(Q)`
then cancels the common suffix action from the empty probe and yields `action(P)=action(R)`.
No longer address is used.

Lean also proves the exact homogeneity needed to compare side-specific cut positions. For every
word `w`,

```text
scale(w)=(3/5)^|w|·(10/9)^{#D(w)},
v₂(scale(w))=#D(w),
v₅(scale(w))=#D(w)-|w|.
```

Hence equal slopes force equal length and equal `D/T` counts.

## Odd-Family Collapse

Allow different cut positions on the two odd-family relation sides. Piecewise action equality and
the valuation theorem first force the cuts to have equal length. A positive proper common cut
would have equal prefix Parikh vectors. The existing odd-family classification leaves only cut
`3`, but the two prefixes are `DTT` and `TTD`, whose affine offsets differ. Therefore every
uniform odd-family single-cut comparator puts the same cut on both sides and that cut is exactly
one endpoint.

`G3-S26` kills both endpoint cases in both relation orientations: the full-prefix endpoint is the
formal prefix cloak, and the zero-prefix endpoint is the certified suffix cloak. Combined, the
odd family is impossible at every single insertion position, including asymmetric proposed cuts.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Empty, `DT`, and `TD` probes force piecewise equal actions | promotion | Lean affine subtraction theorem |
| Equal mixed-prime slopes force equal raw length and Parikh vector | promotion | Lean two-adic/five-adic valuation theorem |
| A nontrivial uniform single-cut physical fork contains a one-sided genuine kernel pair | promotion | Lean composition with reduced `bcbc` raw distinctness |
| An internal odd-family cut yields a uniform address comparator | rejected | Lean proper-prefix action obstruction |
| Different cuts on the two odd-family sides evade the obstruction | rejected | Lean cut-equality theorem |
| Any odd-family single-cut placement realizes the physical fork | rejected | this result plus `G3-S26` |
| Two or more address cuts collapse in the same way | open | the three-probe subtraction no longer isolates one conjugacy seam |
| Another kernel family has no proper equal-action prefix pair | open | family-specific prefix action classification required |
| `M₃(4)` follows | rejected | multi-cut/stateful interleaving, new relations, routing, and converse remain |

## Master Delta

```text
DEAD: every single insertion position in the explicit odd kernel family.
STRUCTURE: every uniform single-cut comparator splits into kernel pairs on its two sides.
LIVE: multi-cut/stateful interleaving, separate two-offset routing, or a new relation with proper kernel subpairs.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, Lean LSP
diagnostics, forbidden-aperture scan, and source scour pass.
