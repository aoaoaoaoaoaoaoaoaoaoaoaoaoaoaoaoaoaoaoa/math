# Virtually Cyclic Discrepancy Audit

**Date:** 2026-08-08  
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `4f2eb7b1211a2ccbbad1a924fc4bdd175170d009` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e223-7170-83ea-9341-375dc86e04f9

## Verdict

Global solvability-only recoding is decidable whenever one computably supplied normal witness per
yes-instance has prefix discrepancies in a finite union of capped periodic rays. The converse may
remain completely global: every arbitrary new witness need only imply an old witness. No local
role decoder, block return, exact side serialization, or normality of all solutions is required.

This removes the entire finite-mode, single-open-carrier lane. A surviving ternary GPCP
construction needs at least two independent unbounded residual factors, genuine word order, or a
halting-dependent normal form unavailable to the reduction.

## Formalized Discrepancy Core

Lean checks the exact free-monoid laws in `WordDiscrepancy.lean`:

- equality after arbitrary continuations forces the original prefixes to be comparable;
- a first internal mismatch is therefore permanent;
- all four signed residual transitions reduce exactly to equations on the unmatched suffix;
- both terminal-boundary tests reduce exactly to one residual equation.

These theorems include erasing images, equality, orientation changes, and arbitrary overlap. They
remove parsing assumptions from the audited automaton construction.

## Audited Decision Theorem

For each finite mode, suppose the live signed residuals lie in a supplied finite set plus finitely
many rays

```text
±u p^n v,       n∈ℕ, p≠ε.
```

The key word equation is

```text
A P^n B = C Q^m D.
```

Lengths place all exponent pairs on at most one arithmetic line. After absorbing its initial
powers, the two moving periodic interiors have equal period length. A fixed window decides whether
they mismatch forever; if they agree, only fixed boundary-junction windows remain. Hence the
solution set is effectively finite plus at most one arithmetic tail.

Applying this to each residual update yields finitely many exceptional transitions and, above an
effective threshold, fixed counter increments subject only to congruence conditions. The
congruences enter finite control. Intersecting with the supplied source-mode automaton produces an
ordinary one-counter automaton. Pushdown reachability decides whether one of the finitely many
terminal discrepancies is reachable; one bit enforces a nonempty source word.

Overlapping ray descriptions do not create false paths: the finite control records the chosen
representation and every inserted edge is certified by its exact word equation. Conversely, a
normal path may choose any valid representation at each step.

The two-power periodicity lemma, effective threshold construction, and one-counter reduction are
independently audited paper proofs, not Lean declarations.

## Reduction Consequence

A computable reduction from the universal Neary family cannot satisfy both:

1. every yes-instance yields some new witness whose complete prefix path has an effectively
   supplied virtually cyclic normal form;
2. every arbitrary new witness implies an old terminal match.

Searching only the decidable normal subclass would already decide the old source. Fixed-length
injective binary target recoding preserves prefixes and periodic rays, so it does not evade the
obstruction.

## Scope

The normal form may have finite caps, both signs, distinct periods by mode, cyclic rotations,
overlapping rays, erasure, regular intended syntax, and a residual left open for arbitrarily many
blocks. Its single restriction is one unbounded periodic degree of freedom per finite mode.

The theorem does not cover two independent exponents such as `up^mvq^nw`, residual families with
unbounded word-order entropy at fixed length, or a normal form which depends on the unknown
halting witness and cannot be computed from the instance.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A first target mismatch is permanent | promotion | Lean theorem `mismatch_persists` |
| Signed residual updates and terminal tests have the displayed exact laws | promotion | Lean transition theorems |
| Two-power word equations are effectively finite plus one arithmetic tail | promotion | independently audited periodicity proof |
| Virtually cyclic normal-witness existence is decidable | promotion | independently audited one-counter reduction |
| State-dependent spelling or an open residual automatically escapes | rejected | both are allowed inside the normal form |
| Every global word-residual construction is decidable | rejected | multi-counter and word-order residuals survive |
| `GPCP(3)` or `M₃(4)` follows | rejected | no ternary compiler is constructed |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every computably supplied finite-mode residual normal form with one unbounded periodic
         carrier, even under global solvability-only converse.
ADDED: exact checked discrepancy dynamics and an audited one-counter decision reduction.
REMAINS: a genuinely word-valued or at-least-two-counter residual, or a halting-dependent normal
         form unavailable to the compiler.
```

## Artifact

- [`WordDiscrepancy.lean`](../MatrixMortality/WordDiscrepancy.lean)
