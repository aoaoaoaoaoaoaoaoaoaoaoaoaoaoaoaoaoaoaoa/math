# Priority-Triangular Transfer Audit

**Date:** 2026-08-11  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `f5b307826d7e5c9750909bdbb2286f58ff22cb85` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3be3-fdfc-83ea-9bdf-e3ecc5f970d8

## Verdict

No ternary compiler or master closure is obtained. The report does close a strictly larger
decidable residual class than `G3-D04`: effectively proper counter atlases with one fixed
priority may use unbounded reset, destructive transfer, fanout, and arbitrary fixed
multiplication, provided every drain deposits only into later counters.

The exact drain stage and strict extension beyond finite translation unions are kernel-checked.
The finite atlas assembly and VASS-with-nested-zero-tests decision theorem remain audited.

## Logical Macro

Fix a pivot `i` and a nonnegative fanout `Aᵢ` with support strictly after `i`. One logical stage
maps

```text
nᵢ ↦ 0,
nₜ ↦ nₜ+nᵢ(Aᵢ)ₜ  for t>i,
```

while earlier counters remain zero. The compiled private VASS mode has the single self-loop

```text
−eᵢ+Aᵢ
```

and can exit only through the nested test that counters `0,…,i` vanish.

If the pivot enters with value `s`, then after `k` loops it contains `s−k`. Natural-state
semantics forbids `k>s`; the exit test forces `s−k=0`, hence `k=s`. The loop therefore has
exactly the logical effect above. Strictly later support preserves every zero already tested.

`PriorityTriangularResidual.lean` proves the bidirectional theorem

```text
NestedZero i source ∧ DrainTransfer i A source target
  ↔ ∃ k, DrainIteration i A k source target ∧ NestedZero (i+1) target.
```

It also proves separately that every drain iteration count is at most the initial pivot and that
an accepting exit count equals it.

## Atlas Assembly

A guarded priority-triangular macro is compiled as follows:

1. Debit the fixed values of the guarded initial segment and test that segment for zero, using
   the already checked `G3-D04` macro.
2. For each consecutive pivot in the requested drain interval, enter a private loop mode and
   use the next nested-prefix test as its only exit.
3. Apply the fixed final integer drift and enter the target logical mode.

Each branch receives private internal modes. Finite unions and finite control therefore remain
finite, and the only tests are one nested hierarchy. Effective properness turns bounded initial
and terminal word residuals into computable finite counter sets. A bit in finite control enforces
the nonempty-witness condition.

Guttenberg, Czerwiński, and Lasota prove reachability decidable for VASS with nested
initial-segment zero tests. The exact source and theorem boundary remain recorded in
[`guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md`](../references/guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md).

## Strict Extension

The one-counter reset `n↦0` is the drain with zero fanout. It cannot be a finite union of fixed
translations: input `n` requires displacement `−n`, giving infinitely many distinct shifts.
Lean proves the finite contradiction with an explicit bound, not a cardinality axiom:

```text
PriorityTriangularResidual.reset_not_finite_translation_union
```

Thus `G3-D05` genuinely extends, rather than merely repackages, the affine translations of
`G3-D04`.

## Consequence

Suppose a computable ternary recoding of the verified Neary family supplies one atlas-normal
witness per yes-instance, exact signed-residual transitions, exact terminal boundary tests, and
an arbitrary-new-word converse. The compiled VASSnz target is reachable exactly when the old
Neary instance halts. Decidable VASSnz reachability would decide the verified source family, a
contradiction.

Malformed new words outside the atlas do not weaken this argument: the normal-form assumption
is used only for the yes direction, while the demanded arbitrary-word converse excludes every
false solution on a no-instance.

## Scope

The result covers one-way destructive drains in one fixed physical priority, including finite
cascades, reset, transfer, fanout, fixed multipliers, affine drift, finite modes, and finite
unions. It does not cover:

- backward transfer or feedback;
- source-preserving copy;
- cyclic reuse of the same priority levels;
- products of unbounded counters or data-dependent multiplication;
- incomparable recurrent tests or changing priority;
- an unbounded free-word residual;
- an atlas unavailable without solving the old instance.

These are the live exits for the global recoding beam.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Natural drain loops cannot overdraw the pivot | formalized | `drainIteration_steps_le` |
| The nested exit fixes the loop count | formalized | `drainIteration_exit_steps` |
| One logical drain equals its VASS gadget in both directions | formalized | `drainTransfer_iff_exitIteration` |
| Reset is not a finite union of translations | formalized | `reset_not_finite_translation_union` |
| Finite priority-triangular atlases compile to VASSnz | audited | private-mode cascade construction |
| VASSnz reachability is decidable | external theorem | Guttenberg-Czerwiński-Lasota, Corollary V.7 |
| Feedback, nonlinear interaction, or changing tests are decidable here | rejected | outside the hypotheses |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: fixed-priority one-way reset, destructive transfer, fanout, and fixed multiplication.
SURVIVORS: feedback, backward/source-preserving transfer, cyclic priority reuse, counter products,
           changing or incomparable tests, irreducible word order, or a noncomputable atlas.
```
