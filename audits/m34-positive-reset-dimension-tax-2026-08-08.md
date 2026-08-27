# Positive Reset Dimension-Tax Audit

**Date:** 2026-08-08  
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `ccc4ac2c72caeea3d4d7f614d69892268c84f672` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e26b-cc2c-83ea-85da-271d150c0488

## Verdict

The report kills the residual-local, projectively full reverse-queue constructor. This is a
strictly positive obstruction: it invokes neither formal inverse words nor the `F₂×F₂` group
action of `G3-O05`.

For a nonempty production body `q`, the legal reverse queue `qb` admits both rule deletions:

```text
qb → q       through the b rule,
qb → ε       through the c rule.
```

If both legal prepend cylinders span the state space, their data maps are invertible. Cancelling
those maps in the two rule/erase comparisons forces the persistent queue states of `q` and `ε`
onto the same projective ray.

## Formal Theorem

`PositiveResetNoGo.positiveReset_collision` quantifies over an arbitrary finite-dimensional
rational vector space, a queue-state map `v`, two data maps, and one phase toggle. Its hypotheses
are the four exact projective transition laws

```text
H_b v_w       ∼ v_bw,
H_c v_w       ∼ v_cw,
H_b T v_{wb}  ∼ v_bw,
H_c T v_{wqb} ∼ v_cw,
```

and fullness of both prepend cylinders. It concludes `v_q∼v_ε`.

Lean separately proves that cylinder fullness forces the corresponding data map to be injective:
every cylinder vector lies in its linear range, hence the range is the whole finite-dimensional
space and surjectivity equals injectivity. The proof then uses the one critical state `qb`; no
malformed control or illegal inverse history occurs.

The standard homogeneous radix queue code is consumed explicitly. The states
`v_a,v_ab,v_ac` in either cylinder have determinant

```text
B²(B−1)(d_b−d_c),
```

which Lean proves symbolically. Every nondegenerate radix, signed-digit, or denominator variant
with the same legal chart therefore satisfies cylinder fullness.

## Scope

The result applies when the persistent legal state depends only on the current reverse queue and
faithfully distinguishes `q` from `ε`, and both complete prepend cylinders span its vector space.
It allows unbounded rational denominators, p-adic heights, and arbitrary behavior outside the
legal locus.

It does not kill a history-sensitive state, a legal cylinder confined to a proper plane, or a
system which deliberately identifies `q` with `ε` while a transient route coordinate rejects
illicit uses. The checked fixed-`bcbc` recognizer survives by exactly those means: singular data
maps and an entrance-history guard.

The paper-level dimension corollary says that a faithful projectively full queue code with vector
span three requires an additional ambient coordinate for the reset, hence at least four vector
dimensions. Lean proves the collision theorem from which this follows; it does not package the
ambient-versus-legal-span dimension inequality as a separate declaration.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Full legal prepend cylinders force injective data maps | promotion | Lean theorem `injective_of_cylinder_span` |
| The legal state `qb` forces `v_q∼v_ε` | promotion | Lean theorem `positiveReset_collision` |
| Ordinary homogeneous radix cylinders span three dimensions | promotion | Lean determinant theorems |
| Denominator or valuation traps repair the critical collision | rejected | the collision occurs wholly on the legal locus |
| Every singular three-state paired compiler is impossible | rejected | history-sensitive and collapsed-cylinder systems remain |
| A faithful full three-vector queue chart requires a fourth ambient coordinate | promotion | audited corollary of the checked collision theorem |
| `M₃(4)` follows | rejected | the surviving history-sensitive singular class is not excluded |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every residual-local faithful queue/deque recurrence with two projectively full legal
         prepend cylinders, including denominator-generating and singular-ideal guards outside
         the legal chart.
ADDED: a positive reset collision at qb and the exact radix-cylinder determinant.
REMAINS: a source-uniform history-sensitive singular recurrence with at least one legal cylinder
         of vector span at most two and a source-computable transient spelling guard.
```

## Artifact

- [`PositiveResetNoGo.lean`](../MatrixMortality/PositiveResetNoGo.lean)
