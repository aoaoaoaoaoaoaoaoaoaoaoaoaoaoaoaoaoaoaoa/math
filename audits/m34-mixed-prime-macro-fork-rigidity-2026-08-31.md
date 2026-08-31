# M₃(4) Mixed-Prime Macro Fork Rigidity Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `fc65cde` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeFork.lean`](../MatrixMortality/GuardedMixedPrimeFork.lean)

## Verdict

The genuine-macro branch left by `G3-S06` is no longer unconstrained. Every exact block-coded
mixed-prime endpoint realization of the `bcbc` suffix language sends the flat and nested terminal
fork blocks to the same affine action on `ℚ`. The expanded fork words must therefore be literally
equal or form a distinct equal-action pair in the mixed-prime kernel. Their actions commute as a
corollary.

The elementary common-fixed-point escape is impossible. If all three control macros fix one
affine point, the endpoint equation accepts a certified rejected suffix. Surviving macros must
have no common affine fixed point and must solve the forced fork relation before any normalized-
mantissa analysis begins.

## Affine Cancellation

For a raw mixed-prime word `w`, define

```text
σ(D)=2/3,       σ(T)=3/5,       σ(w)=∏ σ(letter).
```

Lean proves

```text
wordAction(w,x)−wordAction(w,y)=σ(w)(x−y).
```

Every raw word action is injective. If two word actions fix one point and have the same slope,
the difference formula makes them equal on every rational state. If `w` is nonempty, then
`0<σ(w)<1`, so `w` has a unique affine fixed point.

These results use exact rational arithmetic and apply to empty macros as well, except where
nonemptiness is stated explicitly.

## Fork Cancellation

Let `κ` map the three paired controls to raw `D,T` words. The canonical `bcbc` terminal fork has
a compulsory leading data `c`. Remove that letter and write the remaining fixed terminal prefix
as `P`. Let

```text
x = wordAction(κ(toggle),source),
F₀ = wordAction(κ*(flatForkControl)),
F₁ = wordAction(κ*(nestedForkControl)).
```

The forks indexed by `[]`, `[false]`, and `[true]` are all native zeros. Exact endpoint semantics
therefore gives

```text
P(x)=target,
P(F₀(x))=target,
P(F₁(x))=target.
```

The raw action `P` is injective, including when its word is empty. Cancellation yields

```text
F₀(x)=x=F₁(x).
```

The flat and nested fork controls have the same control counts:

```text
                 data b     data c     toggle
flat fork           8          4          4
nested fork         8          4          4
```

Replacing each control by an arbitrary macro preserves equality of the total raw-word slopes.
The common fixed point and equal slopes then give

```text
F₀(z)=F₁(z)     for every z∈ℚ.
```

Thus exactness forces the explicit dichotomy

```text
κ*(flatForkControl)=κ*(nestedForkControl)
or
κ*(flatForkControl)≠κ*(nestedForkControl)
and the two distinct words induce one mixed-prime affine map.
```

The second branch is a genuine positive-semigroup kernel relation. The first is a free-monoid
morphism equation and must be classified separately; action equality alone does not distinguish
them.

## Common-Fixed Obstruction

Assume all three macro actions fix one affine point `p`. If the endpoint equation were exact,
`G3-S06` would force the three macro actions to be pairwise distinct, so at least one macro is
nonempty. Every paired control occurs in the flat fork, so the expanded flat-fork word is
nonempty and has a unique fixed point.

Fork cancellation says that the same flat action fixes
`x=wordAction(κ(toggle),source)`. It also fixes `p`, hence `x=p`. The toggle macro is injective and
fixes `p`, so `source=p`. Every encoded paired-control word now fixes `p`. The accepted zero-bit
fork forces `target=p`, but the certified rejected `dataBCollisionSuffix` also reaches `p`. The endpoint
equation would declare its nonzero paired coefficient zero, a contradiction.

This obstruction includes triples of distinct powers of one affine word. It does not exclude
macros with distinct fixed points satisfying a genuine mixed-prime relation.

## Joint Boundaries

`G3-S07` independently kills fixed equivariant rank-two symmetric-square leakage on a spanning
three-ray carrier. The present theorem concerns direct two-state affine endpoint dynamics, so it
does not follow from that result; together they remove both the fixed `Sym²` repair and the common-
fixed affine macro repair.

`D2-S08` remains downstream. Its guarded-shell depth shift neither creates the fork relation nor
proves closure of a macro image. A surviving code must first satisfy the relation above, then
supply guarded semantics and shift closure, and still retain the exact normalized mantissa.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every raw mixed-prime word action is injective | promotion | Lean induction |
| Equal slope and one common fixed point determine the entire affine action | promotion | Lean difference formula |
| A nonempty raw word has one affine fixed point | promotion | Lean strict-slope proof |
| Exact endpoint semantics makes both fork blocks fix the toggled source | promotion | three terminal forks and injective cancellation |
| The flat and nested fork actions are globally equal and commute | promotion | equal macro Parikh vectors and affine cancellation |
| Every exact code supplies a literal word equation or a distinct kernel pair | promotion | Lean dichotomy |
| Three macros with one common affine fixed point can be exact | rejected | unique fixed point and certified false suffix |
| Every genuine mixed-prime macro code is impossible | open | non-common-fixed kernel solutions remain unclassified |
| `M₃(4)` follows | rejected | the complete endpoint converse remains open |

## Formal Validation

The owner module and root import compile warning-free under the repository toolchain. The focused
default namespace linter and Lean LSP report no diagnostics. Publication-facing declarations are
listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`. No proof aperture, project axiom, unsafe
declaration, linter suppression, or external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
FORCED FIXED POINT: flat and nested fork blocks both fix the toggled source.
FORCED RELATION: the two fork blocks induce one affine action and commute.
EXACT SPLIT: literal macro word equation or genuine mixed-prime kernel relation.
NO-GO: the three control macros cannot share an affine fixed point.
LIVE ESCAPE: non-common-fixed macros solving the fork relation and the full endpoint converse.
```
