# Positive Common-Shift Countermodel Audit

**Date:** 2026-08-08  
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `77d285f0b7dc27804d3a05be3cdfcb240e087946` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e22e-470c-83ea-875a-b0acebfde4d4

## Verdict

The proposed implication from positive common shifts to the inverse saturation required by
`G3-O05` is false. The report supplies three explicit integral `3 × 3` matrices whose complete
zero language is `{t}`, yet the `b`-shift merges the distinct reachable columns of `ε` and `t`.
The collapse respects every positive prefix-suffix context because neither `b` nor `bt` admits a
left completion to `t`.

Lean reconstructs the algebraic core in `PositiveShiftCountermodel.lean`. This is a counterexample
to the proposed lower-bound bridge, not a compiler for the paired Neary language.

## Checked Countermodel

For `γ=(1,0,0)ᵀ`, `λ=(1,0,1)`, and

```text
H_b=[[0,0,1],[0,0,0],[1,1,1]],
H_c=[[0,0,0],[0,0,1],[1,1,1]],
H_t=[[0,0,0],[1,0,0],[0,1,1]],
```

Lean proves an exact natural-number recurrence for `H_wγ`. Every word is either `ε`, `t`, or
reaches a vector with positive final coordinate. Therefore

```text
λH_wγ=0 ↔ w=t
```

for every free-monoid word. It also proves:

- every generator has rank exactly two, by explicit two-state factorizations with one-sided
  inverses;
- the columns at suffixes `ε,t,b` form the identity matrix;
- the rows at prefixes `ε,t,c` have determinant `−1`;
- no positive matrix product is zero;
- `H_bH_εγ=H_bH_tγ` although `H_εγ≠H_tγ`;
- backward cancellativity therefore fails on the reachable orbit.

The finite context certificates rule out unreachable or unobservable padding as the source of
the collision.

## Audited Semantic Strengthening

The report labels the free positive monoid inside

```text
Γ=(⊕_{i∈ℤ} F(p_i,q_i)) ⋊ ℤ,
b↦p₀, c↦q₀, t↦τ.
```

Splitting a positive word at its `t` letters puts each intervening `{b,c}` block in a distinct
free factor and records the number of `t` letters in the `ℤ` coordinate. This is an injective
positive spelling. The factors at indices zero and one commute with trivial intersection, so
`Γ` contains `F₂×F₂`. Nevertheless the displayed positive column collision precludes any
equivariant inverse extension: cancelling `p₀` would identify the distinct columns of `ε` and
`t`.

This group normal-form argument, the infinite Fibonacci orbit of `H_b^nγ`, and the absence of
nilpotent products are independently audited paper deductions from the displayed formulas; they
are not claimed as Lean declarations. None is needed for the formal backward-cancellation
counterexample.

## Exact Missing Hypotheses

Global reachability, observability, arbitrary-word correctness, an infinite positive orbit, and a
cancellative semantic monoid do not imply inverse saturation. A paired lower bound through
`G3-O05` must prove both:

```text
backward residual cancellativity
+ inverse-orbit cofinality.
```

The first says that a positive cylinder cannot merge two terminal-relevant residuals unless they
were already equivalent. The second says that the formal inverse states needed by the
`F₂×F₂` action are positively represented, or otherwise inherit the target law. Cylinder
spanning would force invertibility on the reachable space, but would not by itself establish the
second condition.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The displayed integral series has zero language `{t}` | promotion | Lean theorem `coefficient_int_eq_zero_iff` |
| Every displayed generator has rank two | promotion | Lean theorem `generator_rank` |
| The realization is fully reachable and observable | promotion | Lean determinant theorems |
| Positive backward cancellativity fails | promotion | Lean theorem `not_backward_cancellative` |
| The semantic positive monoid embeds in a group containing `F₂×F₂` | promotion | independently audited group normal form |
| Positive common shifts force inverse saturation | rejected | explicit checked collision |
| The paired Neary series has such a collision | open | the singleton countermodel does not address it |
| `M₃(4)` follows | rejected | no universal paired compiler is constructed |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: the broad lower-bound bridge from positive common-shift equivariance to G3-O05.
ADDED: a rank-two, reachable-observable, all-word countermodel and the exact two-part hypothesis
       needed by any surviving saturation proof.
REMAINS: prove backward residual cancellativity and inverse-orbit cofinality for the paired
         language itself, or abandon saturation for a different lower bound.
```

## Artifact

- [`PositiveShiftCountermodel.lean`](../MatrixMortality/PositiveShiftCountermodel.lean)
