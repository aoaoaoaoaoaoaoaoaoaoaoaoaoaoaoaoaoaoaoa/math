# M₃(4) Uniform Terminal-Coefficient Section Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `3679b19` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseInfiniteAtlas.lean`](../MatrixMortality/TransverseInfiniteAtlas.lean)

## Verdict

For every rational source, one pole-free source-dependent column makes the fixed-row terminal
coefficient map surjective onto `ℚ³`. Every scalar `A−B2ⁿ−C3ⁿ` from `G3-O32` is therefore
realizable by an explicit total rational row. In particular, any source-indexed target depth can
be selected as an exact delayed singleton.

This closes algebraic restrictions on source-dependent rows or columns as a lower-bound route for
the explicit `G3-O30` carrier family. It does not construct the required history-to-depth map on
the raw control monoid.

## Pole-Free Section

Fix `s∈ℚ` and use the column

```text
γ_s = (s²+1,1,0).
```

The two relevant factors never vanish. Lean proves

```text
s²+1 > 0,
s²+s+1 > 0.
```

The second inequality follows from `(2s+1)²≥0`; no case split or algebraic extension is used.
Given an arbitrary target coefficient vector `(A,B,C)`, define

```text
λ_{s,A,B,C} = (A/(s²+s+1), B/(s²+1), C).
```

Writing `γ_s=(x,y,0)` and `λ=(a,b,c)`, the three `G3-O32` coefficients reduce exactly to

```text
a(x+sy) = A,
bx       = B,
cy       = C.
```

Thus, at every depth `n`,

```text
λ_{s,A,B,C}(TⁿD_sγ_s) = A − B2ⁿ − C3ⁿ.
```

Lean represents the coefficient triple as a three-coordinate state and proves that the displayed
row is a right inverse. The map

```text
λ ↦ (A,B,C)
```

is formally surjective with `s` and `γ_s` fixed.

## Arbitrary Delayed Targets

Let `Σ` be any source type, `s:Σ→ℚ` any parameter map, and `N:Σ→ℕ` any target-depth
function. Substitute

```text
(A,B,C) = (2^N(σ),1,0)
```

in the coefficient section. Lean proves, for every `σ∈Σ` and `n∈ℕ`,

```text
λ_σ(TⁿD_{s(σ)}γ_{s(σ)}) = 0  ⇔  n=N(σ).
```

The proof reduces to injectivity of `n↦2ⁿ`. No boundedness, regularity, or injectivity hypothesis is
placed on `N`. Lean's theorem is function-parametric rather than computability-theoretic; when
`s` and `N` are computable, the displayed field operations and natural power make the resulting
row and column computable.

## Boundary Of The Cut

The section controls the terminal row and initial point on the special prefix carrier
`TⁿD_s`. It does not provide any of the following:

1. a generator family that sends an arbitrary valid terminal history to depth `N(σ)`;
2. distinct behavior for the two paired data controls;
3. a same-zero equivalence on the complete free control monoid;
4. a mechanism excluding nonterminal or malformed words;
5. more than the at-most-two point incidences allowed by `G3-O32`;
6. a decision or undecidability result for `M₃(4)`.

The negative lesson is exact. Any argument using only poles, denominator vanishing, coefficient
rank, or algebraic range of a source-dependent terminal row is dead for this family. A surviving
obstruction must act on the word dynamics that produces the depth or on the whole moving carrier
section.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Both denominator polynomials are positive over `ℚ` | promotion | Lean theorems `source_sq_add_one_pos`, `source_sq_add_source_add_one_pos` |
| The displayed row recovers every prescribed coefficient triple | promotion | Lean theorem `terminalCoefficients_section` |
| The fixed-column row-to-coefficient map is surjective | promotion | Lean theorem `terminalCoefficients_surjective` |
| The realized terminal scalar is exactly `A−B2ⁿ−C3ⁿ` | promotion | Lean theorem `coefficientSection_terminalValue` |
| Every source-indexed target depth is an exact singleton | promotion | Lean theorem `coefficientSection_sourceFamily_delayed_zero_iff` |
| Every such family is computable without hypotheses | rejected | computability requires computable input maps `s` and `N` |
| Arbitrary histories can be compiled to the selected depth | rejected | no history-to-depth dynamics is constructed |
| The full nonprojective architecture is universal | rejected | only terminal coefficients on `TⁿD_s` are parameterized |
| `M₃(4)` follows | rejected | no same-zero compiler or arbitrary-word converse is proved |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain. Publication-facing
declarations are listed in [`AxiomAudit.lean`](../AxiomAudit.lean). Their selected transitive
axiom outputs contain only the reviewed standard axioms. No `sorry`, `admit`, project axiom,
unsafe declaration, suppression, or proof aperture is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
CLOSED: algebraic source-to-row or source-to-column range restrictions for the G3-O30 point test.
POSITIVE: every rational coefficient triple and every source-indexed delayed singleton is
          attained by one total rational section.
SURVIVOR: construct or exclude the history-to-depth map on the complete three-control monoid.
```
