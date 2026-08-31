# Prefix-Height Rate Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `8a92466` on `wave3-m34-ucb`

**Salvage record:** `D2-O12`

## Verdict

The height escape forced by `D2-O06` has an exact finite-family rate. Let a
finite type index `N` pairwise distinct group prefixes acting on a rational
projective target with trivial stabilizer. Choose a primitive integral pair
for every target-orbit state and suppose every pair has height at most `H`.

Two equal pairs would give equal projective states. The quotient of their
distinct prefixes would then be a nonidentity target stabilizer, contradicting
the hypothesis. Hence the pairs inject into the integer square
`[-H,H]²∩ℤ²`, and

```text
N ≤ (2H+1)².
```

Lean also checks the exact threshold contrapositive:

```text
(2H+1)² < N  ⇒  ∃ represented state of height > H.
```

For the unique-coset application, a known hit from a trivial-stabilizer source
conjugates any target stabilizer back to the source, so every promised
yes-instance inherits target-stabilizer triviality.

## What The Rate Controls

The theorem bounds the number of distinct prefixes whose states can all fit
below one height ceiling. It controls the maximum height over each finite
family. It does not assert

```text
height(state i) < height(state (i+1)),
```

nor any weaker eventual monotonicity. A path may escape above `H`, return
below `H`, and escape again. The theorem only prevents more than `(2H+1)²`
distinct prefix states from lying inside that cube in total.
`D2-O13` subsequently packages this finite-return consequence as convergence
of height to infinity.

The square is a containing count rather than a sharp primitive-ray count. It
includes zero, noncoprime pairs, and both signs. Sharpening the constant would
not by itself decide the unbounded branch.

## Formalization

`prefix_count_le_height_square_of_stabilizer_trivial` maps every represented
state into the explicit cube from `D2-O10`. Target-stabilizer triviality makes
that map injective: an equality produces the nonidentity quotient already
formalized in `exists_nontrivial_stabilizer_of_orbit_collision`. Finite-type
cardinality then gives the displayed square bound.

`exists_height_gt_of_square_lt_prefix_count` is the exact contrapositive. The
companion theorem
`target_stabilizer_trivial_of_reachable_from_trivial_source` formalizes the
promise-side conjugation transfer.

## Verification

The following checks pass in the isolated worktree:

```text
lake build MatrixMortality.InverseOrbitRecurrence
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every publication-facing theorem is listed in `AxiomAudit.lean` and depends
only on the reviewed Mathlib axioms. No project axiom, proof aperture, warning
suppression, reference PDF, or external literature premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `N` distinct prefixes below height `H` satisfy `N≤(2H+1)²` at a trivial-stabilizer target | promotion | Lean-checked injection into the exact cube |
| `(2H+1)²<N` forces some state above `H` | promotion | Lean-checked exact contrapositive |
| A known hit transports trivial source stabilizer to the target | promotion | Lean-checked conjugation |
| Prefix height grows monotonically | rejected | only the finite-family maximum is controlled |
| The first height escape is permanent | rejected | later finite returns remain possible |
| General `UCB₂(S)` is decidable | open | no complete unbounded-path invariant is supplied |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: rate-free unbounded escape as the description of the residual branch.
ADDED:   the exact finite-family constraint N≤(2H+1)² and its threshold
         contrapositive.
REMAINS: bound returns to smaller height cubes or find a secondary invariant
         that turns repeated escapes into termination or separation.
```

## Artifacts

- [`InverseOrbitRecurrence.lean`](../MatrixMortality/InverseOrbitRecurrence.lean)
- [`D2-O12`](../SALVAGE.md#d2-o12-exact-prefix-height-rate)
