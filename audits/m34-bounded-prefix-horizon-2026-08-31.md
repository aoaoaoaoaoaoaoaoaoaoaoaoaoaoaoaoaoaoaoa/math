# Bounded-Prefix Horizon Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `e5b2dad` on `wave3-m34-ucb`

**Salvage record:** `D2-O10`

## Verdict

The bounded branch isolated by `D2-O06` has an explicit finite horizon. A
primitive integral pair of maximum-coordinate height at most `H` lies in

```text
[-H,H]² ∩ ℤ²,
```

which has exactly `(2H+1)²` elements. Given `(2H+1)²+1` distinct group
prefixes acting on one rational projective target, if every image is supplied
with a primitive representative of height at most `H`, two representatives
coincide. If they occur at prefixes `gᵢ≠gⱼ`, then

```text
gᵢq=gⱼq,       (gⱼ⁻¹gᵢ)q=q,       gⱼ⁻¹gᵢ≠1.
```

Thus the finite window exposes a nonidentity target stabilizer. If the target
stabilizer is trivial, some state in that same window has height greater than
`H`.

The result closes bounded inverse search as an asymptotic branch: a computable
normal-form parser need only inspect this finite window before obtaining either
a height escape or a stabilizer witness. It does not control the unbounded
branch or decide whether an arbitrary target stabilizer is trivial.

## Formalization

`InverseOrbitRecurrence.lean` adds:

1. `integralPairCube`, the explicit integer square of radius `H`;
2. `integralPairCube_card`, its exact cardinality `(2H+1)²`;
3. `mem_integralPairCube_of_pairHeight_le`, the height-to-cube inclusion;
4. `exists_nontrivial_stabilizer_of_bounded_prefix_window`, the finite
   collision theorem; and
5. `bounded_prefix_window_escape_of_stabilizer_trivial`, its
   trivial-stabilizer contrapositive.

The older finiteness proof now factors through the same cube, so the qualitative
and quantitative theorems have one cardinality owner.

## Scope

The horizon is uniform but not sharp. The containing square counts the zero
pair, noncoprime pairs, and both signs of every projective ray. Removing those
states could reduce the bound but would not change the strategy tree.

The theorem requires pairwise distinct group prefixes. Repeated syntax for the
same group element must first be reduced to a faithful normal form. It assumes
primitive representatives are available and makes no claim that height is
monotone. A branch may cross above `H` and later return below it.

## Verification

The following checks pass in the isolated worktree:

```text
lake env lean MatrixMortality/InverseOrbitRecurrence.lean
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every added publication-facing theorem is listed in `AxiomAudit.lean`. No
project axiom, proof aperture, warning suppression, reference PDF, or external
literature premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The integer cube of radius `H` has `(2H+1)²` elements | promotion | Lean-checked exact cardinality |
| Height at most `H` places an integral pair in that cube | promotion | Lean-checked coordinate bounds |
| `(2H+1)²+1` distinct bounded prefixes force a nonidentity target stabilizer | promotion | Lean-checked finite pigeonhole and quotient action |
| Trivial target stabilizer forces escape above `H` inside that window | promotion | Lean-checked contrapositive |
| The displayed horizon is minimal | rejected | the cube deliberately contains impossible and duplicate ray representatives |
| Unbounded height gives a terminating or finite search | open | no monotonicity or return bound is proved |
| General `UCB₂(S)` is decidable | open | stabilizer recognition and unbounded paths remain |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: an asymptotically bounded but aperiodic inverse branch after D2-O06.
ADDED:   the explicit bounded-prefix horizon (2H+1)²+1 and a finite
         stabilizer-or-height-escape dichotomy.
REMAINS: decide target stabilizers effectively and control the forced
         unbounded-height branch.
```

## Artifacts

- [`InverseOrbitRecurrence.lean`](../MatrixMortality/InverseOrbitRecurrence.lean)
- [`D2-O10`](../SALVAGE.md#d2-o10-finite-bounded-prefix-horizon)
