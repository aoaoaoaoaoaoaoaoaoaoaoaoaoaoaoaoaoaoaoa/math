# M₃(4) Terminal Point-Incidence Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `3646187` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseInfiniteAtlas.lean`](../MatrixMortality/TransverseInfiniteAtlas.lean)

## Verdict

Every fixed rational row-column test on the explicit infinite carrier orbit of `G3-O30` has one
of two zero-depth sets: all natural depths, or at most two depths. The finite bound is sharp. No
search horizon can be uniform in the terminal row, because a singleton zero can occur at any
prescribed depth.

This is a point-incidence sparsity theorem. It does not decide or kill source-computed delayed
targets, moving line sections as a whole, or the nonprojective architecture.

## Exact Scalar

For source `s`, toggle depth `n`, and column `γ=(x,y,z)`, the formal carrier action is

```text
TⁿD_sγ = (x+sy,−2ⁿx,−3ⁿy).
```

An arbitrary terminal row `λ=(a,b,c)` therefore evaluates to

```text
f(n) = λ(TⁿD_sγ) = A − B2ⁿ − C3ⁿ,

A = a(x+sy),             B = bx,             C = cy.
```

The third coordinate of `γ` disappears because `D_s` has zero third column. No sign,
nondegeneracy, or integrality hypothesis is imposed on the remaining data.

## Three-Zero Cut

Assume `f(n₀)=f(n₁)=f(n₂)=0` for `n₀<n₁<n₂`, and put
`p=n₁−n₀>0`, `q=n₂−n₁>0`. Subtracting the equation at `n₀` from the later two
gives a homogeneous two-by-two system in `B` and `C`. After removing the nonzero factors
`2ⁿ⁰` and `3ⁿ⁰`, its determinant is

```text
Δ(p,q) = (2ᵖ−1)(3ᵖ⁺ᵠ−1) − (3ᵖ−1)(2ᵖ⁺ᵠ−1).
```

Lean proves `Δ(p,q)>0` for all positive `p,q`. The proof has the static recurrence

```text
Δ(p,1)   = 3ᵖ(2ᵖ−2)+2ᵖ,

Δ(p,q+1) = 3Δ(p,q) + 2(2ᵖ−1) + (3ᵖ−1)(2ᵖ⁺ᵠ−2).
```

Every term required to be nonnegative is exposed before the final positivity leaf. The
determinant then forces `C=0`; the first difference equation forces `B=0`; the original equation
forces `A=0`.

Lean removes the ordering by trichotomy, extracts any hypothetical three-element subset from the
extended-natural cardinal, and proves

```text
(A,B,C) ≠ (0,0,0)  ⇒  encard {n | A−B2ⁿ−C3ⁿ=0} ≤ 2.
```

It separately proves that the zero set is `Set.univ` exactly when all three coefficients vanish.

## Sharpness

The upper bound occurs inside the actual matrix family, not merely in the abstract scalar
sequence. With

```text
λ = (−1,−2,1),             s=0,             γ=(1,1,0),
```

the scalar is `−1+2·2ⁿ−3ⁿ`, which vanishes at the distinct depths `0` and `1`. The cardinal
bound excludes any third zero.

There is also no terminal-data-independent horizon. For arbitrary `N`, take

```text
λ_N = (2ᴺ,1,0),             γ=(1,0,0).
```

Then `λ_N(TⁿD_sγ)=2ᴺ−2ⁿ`, independently of `s`, and injectivity of rational powers of two
gives

```text
λ_N(TⁿD_sγ)=0  ⇔  n=N.
```

Thus sparsity cannot be strengthened to a uniform bounded-depth search while the row may depend
on the source.

## Boundary Of The Cut

The theorem fixes one quadruple `(λ,s,γ,n)` family and varies only `n`. It does not prove any of
the following:

1. that a source algorithm cannot compute coefficients selecting its required terminal depth;
2. that the moving line `C_n(s)∩ker λ` contains no useful body-dependent point;
3. that finitely many row-column tests cannot be combined;
4. that arbitrary raw words reduce to the prefix family `tⁿb`;
5. that `M₃(4)` is decidable or undecidable.

A positive construction must now make an at-most-two-element depth set carry the entire paired
zero condition and prove the converse for every malformed word. A negative result must constrain
the source-to-coefficient map or the whole moving line, rather than ask one fixed point test for a
richer zero set.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The terminal scalar is `A−B2ⁿ−C3ⁿ` | promotion | Lean theorem `terminalValue_eq_exponentialScalar` |
| The generalized-Vandermonde minor is positive | promotion | Lean theorem `exponentialMinor_pos` |
| Three zero depths force the identity sequence | promotion | Lean theorem `coefficients_eq_zero_of_three_zeros` |
| A nonidentity point test has at most two zero depths | promotion | Lean theorems `exponentialScalar_zeroSet_encard_le_two`, `terminalValue_zeroSet_encard_le_two` |
| The identity case accepts every depth, and only that case does | promotion | Lean theorems `exponentialScalar_zeroSet_eq_univ_iff`, `terminalValue_zeroSet_eq_univ_iff` |
| The zero set `{0,1}` is attained in the carrier family | promotion | Lean theorem `terminalValue_two_zeroSet_eq` |
| Singleton acceptance has no uniform horizon | promotion | Lean theorem `delayedRow_terminalValue_eq_zero_iff` |
| The moving proper line sections are decidable | rejected | only one fixed point on each carrier is classified |
| Source-computed delayed targeting is impossible | rejected | the delayed-row theorem exhibits it exactly |
| The nonprojective architecture is closed | rejected | source dependence and arbitrary-word dynamics remain live |
| `M₃(4)` follows | rejected | no paired recognizer or full converse is constructed |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain. Publication-facing
declarations are listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom output
is compared against [`verification/axioms.txt`](../verification/axioms.txt). No `sorry`, `admit`,
project axiom, unsafe declaration, suppression, or proof aperture is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: three-or-more-depth acceptance by one fixed point test on the G3-O30 carrier orbit.
SHARP: the surviving fixed-point zero set is all depths or at most two; two is attained.
SURVIVOR: source-computed delayed singleton/two-depth targets, whole moving lines, broader
          terminal geometry, and the complete arbitrary-word converse.
```
