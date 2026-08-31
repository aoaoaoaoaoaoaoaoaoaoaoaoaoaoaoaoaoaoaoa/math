# Bounded-Branch Nonreachability Certificate Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `78a1c2e` on `wave3-m34-ucb`

**Salvage record:** `D2-O11`

## Verdict

The finite collision from `D2-O10` is already a nonreachability certificate
under the source-freeness invariant of the unique-Borel-coset problem.

Let a group `G` act on a set, let `p` be the source, and let `q` be the target.
Assume `Stab_G(p)={1}`. If `s≠1` fixes `q`, then no `g∈G` sends `p` to `q`.
Indeed, a hypothetical transporter gives

```text
(g⁻¹sg)p = g⁻¹s(gp) = g⁻¹sq = g⁻¹q = p,
```

so `g⁻¹sg=1` by source-stabilizer triviality, and conjugating back contradicts
`s≠1`.

Now take `(2H+1)²+1` distinct prefixes acting on `q`. If their primitive states
all have height at most `H`, `D2-O10` supplies the nonidentity target
stabilizer `s`; the conjugation theorem certifies that `q` is unreachable from
`p`. Without assuming boundedness in advance, the finite window yields

```text
height escape above H  or  target nonreachability.
```

Thus target-stabilizer recognition is not an independent obligation on the
bounded branch. The unbounded-height branch remains open.

## Formalization

`InverseOrbitRecurrence.lean` adds four theorems:

1. `target_stabilizer_trivial_of_reachable_from_trivial_source`, transport of
   stabilizer triviality through a known hit;
2. `target_unreachable_of_source_stabilizer_trivial`, the abstract
   conjugation certificate;
3. `target_unreachable_of_bounded_prefix_window`, its composition with the
   exact finite horizon; and
4. `height_escape_or_target_unreachable`, the unconditional window
   dichotomy.

All group multiplications and actions are explicit. The proof does not assume
that the target stabilizer is trivial; finding a nontrivial target stabilizer
is precisely the negative certificate.

## Scope

The result assumes trivial source stabilizer, injective group prefixes, and
primitive representatives realizing the target-orbit states. These are
hypotheses, not algorithms constructed here. The theorem decides a supplied
bounded window. It does not bound later heights, prove monotonic escape,
recognize a stabilizer before a collision, or decide general `UCB₂(S)`.

## Verification

The following checks pass in the isolated worktree:

```text
lake build MatrixMortality.InverseOrbitRecurrence
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every added publication-facing theorem is listed in `AxiomAudit.lean` and
depends only on the reviewed Mathlib axioms. No project axiom, proof aperture,
warning suppression, reference PDF, or external literature premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Reachability transports trivial source stabilizer to the target | promotion | Lean-checked conjugation argument |
| A nonidentity target stabilizer forbids reachability from a trivial-stabilizer source | promotion | Lean-checked conjugation argument |
| A bounded `(2H+1)²+1` prefix window certifies target nonreachability | promotion | Lean-checked composition with `D2-O10` |
| Every such window either escapes above `H` or certifies nonreachability | promotion | Lean-checked finite dichotomy |
| Target-stabilizer recognition remains necessary on the bounded branch | rejected | the collision itself constructs the required stabilizer witness |
| A height escape is permanent or monotone | open | the theorem controls only the finite window |
| General `UCB₂(S)` is decidable | open | complete normal forms and unbounded paths remain |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: effective target-stabilizer recognition as a separate obligation on
         a supplied bounded inverse branch.
ADDED:   a finite height-escape-or-nonreachability dichotomy under the
         promised trivial source stabilizer.
REMAINS: construct complete inverse normal forms and control their
         unbounded-height branches.
```

## Artifacts

- [`InverseOrbitRecurrence.lean`](../MatrixMortality/InverseOrbitRecurrence.lean)
- [`D2-O11`](../SALVAGE.md#d2-o11-bounded-branch-nonreachability-certificate)
