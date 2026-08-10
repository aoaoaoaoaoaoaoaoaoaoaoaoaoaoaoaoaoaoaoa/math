# Priority-Affine Residual-Atlas Audit

**Date:** 2026-08-10  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `bc322c4714a59af0721727bf64b476557579c469` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a796368-1c80-83ea-a620-db482d1d7f49

## Verdict

No global three-pair recoding or master closure is obtained. The report does prove a broad
decidability boundary which strictly subsumes the earlier virtually-cyclic, one-counter case:
every computable finite-dimensional proper affine residual atlas with one nested hierarchy of
prefix-equality guards reduces to reachability in a VASS with nested zero tests.

The reduction's arithmetic macro is kernel-checked. The finite atlas assembly and the imported
VASSnz reachability theorem are audited rather than reimplemented.

## Atlas Theorem

Let modes `q` and natural counters `n∈N^d` decode to signed word residuals `ρ(q,n)`. Assume:

1. bounded residual length has an effectively bounded counter preimage;
2. every exact update is a finite union of translations `n↦n+v`;
3. each translation guard fixes the first `j` counters to constants, for one global ordering;
4. initial and terminal residual conditions have bounded length.

Properness makes the initial and terminal counter sets finite. For a guard `n_i=k_i` on `i<j`,
subtract `k_i` from those counters. The transition is enabled only when subtraction remains
nonnegative; a nested zero test on the first `j` counters then forces equality rather than mere
inequality. Restoring `k_i` while adding the drift vector produces exactly `n+v`. Finite modes
and finite unions become ordinary VASS control states and edges.

Guttenberg, Czerwiński, and Lasota prove reachability decidable for VASS with precisely these
nested initial-segment zero tests, with an `Fω` upper bound. Thus reachability through the atlas
is decidable. If a reduction has an arbitrary-word soundness converse and supplies at least one
atlas witness on every yes-instance, this normal-witness search decides the old source predicate.

## Checked Transition Seam

`PriorityAffineResidual.lean` defines natural counter states with integer shift vectors. Lean
proves the equivalence

```text
prefix-value guard + translation
  ↔ debit + nested zero test + credit.
```

Both directions include natural-state nonnegativity. Lean also proves that a larger initial-
segment zero test implies every smaller one, matching the required nested priority.

## External Source Audit

The exact required theorem is Corollary V.7 of arXiv `2502.07660v2`: VASSnz reachability is in
`Fω`. Section III defines a nested test as a zero test on `{1,…,j}`. The complete v2 text was
inspected from an ephemeral PDF with SHA-256
`e86eb337e11c7ace88b7364c9612c8d7fe384036d2bca97c141397f1ea68020d`. No redistribution license
was located, so the repository retains a metadata-only synopsis rather than the source bytes.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A prefix-value affine guard compiles to one nested-zero-test macro | promotion | `guardedTranslation_iff_nestedZeroMacro` |
| Nested zero tests are ordered by their prefix cut | promotion | `nestedZero_mono` |
| Reachability for VASSnz is decidable | external theorem | Guttenberg-Czerwiński-Lasota, Corollary V.7 |
| Every effectively proper priority-affine residual atlas is decidable | audited | finite reduction to VASSnz |
| Reversals, finite sign modes, and arbitrary fixed dimension evade the theorem | rejected | absorbed into finite control and counters |
| Incomparable tests or nonadditive transfers are decidable here | rejected | outside the nested affine hypotheses |
| The global word-residual leaf is closed | rejected | genuinely ordered or non-priority residues remain |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every finite-dimensional fixed-priority affine-counter normal witness class.
SURVIVORS: incomparable recurrent tests, changing priority, transfer/reset/copy operations,
           genuinely unbounded word order, or a noncomputable halting-dependent atlas.
CROSS-POLLINATION: the positive exponent cover survives by carrying a free word plus cocycle,
                   not a finite tuple of priority-affine exponents.
```

## Artifacts

- [`PriorityAffineResidual.lean`](../MatrixMortality/PriorityAffineResidual.lean)
- [`guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md`](../references/guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md)
