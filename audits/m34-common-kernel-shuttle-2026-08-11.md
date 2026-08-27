# Common-Kernel Shuttle Audit

**Date:** 2026-08-11  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `7bc1aa5dc7e48b1a9ef8e1462fe4cd78de67a30e` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3bc9-2cd8-83ea-84cc-b7b53033e7a3

## Verdict

The report does not construct a source-uniform paired recognizer. Its explicit `bcbb` matrices,
all-word recurrence, terminal grammar, modular converse, and mortality lift are already the
formalized result `G3-O06`. The fixed instance is therefore a restatement, not another compiler
ratchet.

The kernel diagnosis is new and correct. Both data controls have common kernel
`K=ℚ(1,1,0)`, but the phase toggle sends its generator to `(1,-1,0)`, outside `K`; either next
data control then sends that vector to `(2,0,0)`. Thus the checked periodic recognizer is an
explicit useful non-invariant common-kernel shuttle. Paired shift equations do not force toggle
invariance.

When the toggle does preserve `K`, the report's quotient factorization is the scalar form of the
existing `G3-S02` route-erasure theorem: two states differing only in a freshly minted kernel
guard remain kernel-separated through the toggle run and the next data action erases the
difference. This closes invariant-kernel persistence, but not two-dimensional quotient dynamics
or the non-invariant shuttle.

## Checked Seam

`PeriodicHistory.lean` now proves:

```text
H_b v=0 ↔ v₂=0 ∧ v₀=v₁,
H_c v=0 ↔ v₂=0 ∧ v₀=v₁,
H_t(1,1,0)ᵀ=(1,-1,0)ᵀ,
H_bH_t(1,1,0)ᵀ=H_cH_t(1,1,0)ᵀ=(2,0,0)ᵀ.
```

These statements include exact kernel equality and nonzero re-emergence; no rank inference or
projective normalization is used.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Toggle-invariant common-kernel guards factor through the two-dimensional quotient after the next data action | restatement | `G3-S02` plus the report's direct factorization |
| The paired laws force `T(K)⊆K` | rejected | checked `bcbb` matrices |
| A useful non-invariant common-kernel shuttle exists | promotion | four new `PeriodicHistory` theorems |
| The displayed matrices recognize the complete `bcbb` language | restatement | existing `G3-O06` formalization |
| The construction is uniform in `(β,body)` | rejected | its boundary constants encode the fixed periodic terminal ray |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: the toggle-invariant common-kernel refresh subcase; any no-go deriving toggle invariance
         from the paired shift laws alone.
SURVIVOR: a source-uniform non-invariant kernel shuttle, or quotient dynamics whose terminal
          section is not a computable finite target family.
TREE CHANGE: common-kernel refresh is renamed common-kernel shuttle; the existing fixed compiler
             witnesses the mechanism but does not solve its uniformity obstruction.
```

## Artifact

- [`PeriodicHistory.lean`](../MatrixMortality/PeriodicHistory.lean)
