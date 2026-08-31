# M₄(3) opposite right-`c` defect cylinder audit

**Date:** 31 August 2026

**Status:** the shortest `1|2|0` bad run with letters `b|c|c` is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** remove one of the seven shortest parabolic exterior-collision survivors

## Verdict

At deletion width three, let `L` and `M` be the lower code and scale of an arbitrary nonempty
body, and put

```text
D = M−3,
A = 16274467L−5515409M−229072,
B = 48637017L−16433267M−839712.
```

Lean proves

```text
det bridge(27, b(3z+1)c(3x+2)c(3y))
  = 729z/4 · (D A y + B − 166944D(Dy+3)x).
```

If the bracket vanished, `x` would be the weighted average of

```text
A/(166944D)  and  B/(500832D)
```

with positive weights `Dy` and `3`. Every nonempty body is either `c^k` with `k>0` or has the
form `c^k b tail`. Exact ternary-coordinate inequalities put both endpoints in these intervals:

| Body cylinder | Common root interval |
| --- | --- |
| `b tail` | `(59,60)` |
| `c b tail` | `(62,63)` |
| `c² b tail` | `(63,64)` |
| `c^k b tail`, `k≥3` | `(64,65)` |
| `c^k`, `k>0` | `(64,65)` |

No interval contains a natural number. The bracket is therefore nonzero for all natural `x,y`;
the regular endpoint condition `z>0` makes the determinant nonzero.

## Proof Boundary

`ParabolicBlade.bridge_bOne_cTwo_cZero_det` substitutes the exact primal residue-one `b`,
residue-two `c`, and residue-zero `c` atom matrices into the checked bridge. The cylinder proof
uses the native tag encoding and its exact rational code bounds. Exterior transport enters only
through the already checked bridge determinant; no primal atom is identified with its
adjugate-transpose exterior action. No body enumeration, floating-point estimate, sampled wait
bound, or external solver certificate enters the theorem.

## Scope

The theorem treats exactly three atoms at `β=3`, orientation `1|2|0`, and letters `b|c|c`. It
does not treat the opposite orientation, a `c` left endpoint, longer residue-two runs, or
nontrivial safe endpoint contexts. Six shortest families remain.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean `4.33.1`.
The two public theorems have transitive axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
