# M₄(3) opposite c-defect cylinder audit

**Date:** 30 August 2026

**Status:** the shortest `1|2|0` bad run with a `c` defect and `b` endpoints is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** close the opposite orientation left open by `M4-S10`

## Verdict

At deletion width three, let `L` and `M` be the lower code and scale of an arbitrary nonempty
body. The checked determinant of

```text
b(3z+1) c(3x+2) b(3y)
```

is `−4374z` times

```text
A(8y+1)x − 8B₁y − B₀,

A  = 1699776(M−3),
B₀ = 164500347L−55585393M−2843496,
B₁ = B₀+247806(M−3).
```

Here `A>0`, and

```text
(B₁−B₀)/A = 1059/7264 < 1.
```

If the bracket vanished, `x` would be the weighted average of the two roots `B₀/A` and `B₁/A`
with weights `1` and `8y`. Every body is either `c^k` or `c^k b tail`. Lean derives

```text
tagEncode₃(c^k b tail)
  = true^k · true false false false true · tagEncode₃(tail),
```

and the corresponding exact ternary code and scale. The root intervals are then:

| Body cylinder | Root interval | Consequence |
| --- | --- | --- |
| `b tail` | `(58,60)` | only `x=59`; the root weight forces `y<1`, then `y=0` contradicts the strict base-root bound |
| `c b tail` | `(62,63)` | no natural `x` |
| `c² b tail` | `(63,64)` | no natural `x` |
| `c³ b tail` | `(63,65)` | only `x=64`; the root weight forces `y<1`, then `y=0` contradicts the strict base-root bound |
| `c^k b tail`, `k≥4` | `(64,65)` | no natural `x` |
| `c^k`, `k>0` | `(64,65)` | no natural `x` |

Thus the bracket and determinant are nonzero for all nonnegative `x,y` and regular `z>0`.

## Proof Boundary

`ParabolicBlade.bridge_bOne_cTwo_bZero_det_ne_zero` consumes the exact determinant and coefficient
gap from `MatrixMortality.ParabolicDefect`. The new module proves the body decomposition, ternary
prefix equations, cleared root bounds, and the two single-candidate contradictions in Lean. No
floating-point estimate, enumerated body-length cutoff, external solver certificate, or unproved
asymptotic step enters the theorem.

The argument treats natural waits directly. It does not infer nonvanishing from a sampled range.
The all-`c` family is proved for every positive length, and the final cylinder is proved uniformly
for every leading run length `k≥4`.

## Scope

The result treats exactly three atoms at `β=3`, with `b` safe endpoints and a `c` defect in the
`1|2|0` orientation. It does not cover a `c` endpoint, a longer defect run, or a nontrivial safe
context at either endpoint. The hypothesis `z>0` excludes the exceptional singular endpoint
`b(1)`.

Together with `M4-S10`, this eliminates both shortest bad-run orientations with a `c` defect and
`b` endpoints. It does not decide `M₄(3)`.

## Validation

`MatrixMortality.ParabolicDefect` and `MatrixMortality.ParabolicDefectCylinder` build without
warnings under Lean `4.33.1`. Fresh Lean LSP diagnostics report no errors, warnings, information,
or hints. The publication theorem has axiom set exactly `[propext, Classical.choice, Quot.sound]`.
No proof aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
