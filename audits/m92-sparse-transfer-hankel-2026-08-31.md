# M₉(2) sparse transfer-Hankel audit

Date: 2026-08-31
Record: `MM-O24`
Evidence: formalized late branch; audited early assembly

## Hypotheses

Let a binary generator factor through the four-coordinate paired interface,

```text
B=UV,     Mᵣ=VAʳU,
```

where `A` is an arbitrary `n × n` transition. Fix three distinct run lengths `t,b,c`. Assume

```text
Mₜ=aT,     M_b=dD_b,     M_c=eD_c,     a,d,e≠0,
```

for the exact paired roles at deletion width three and body `bb`, and assume `Mᵣ=P′` after all
three exceptional positions. Earlier intervening moments are unrestricted. No direct-sum parser
fibres, deterministic decoder state, or common-image quotient is assumed.

The conclusion is `n≥10`. If the last exceptional position is at least three, the stronger
bound `n≥11` holds. The result concerns exact matrix-valued moments and a constant rank-one
tail. It does not constrain a compiler which preserves only the zero set while changing its
nonzero moments, a nonconstant safe tail, or nonlinear boundary semantics.

## Late exception

Put `Dᵣ=Mᵣ-P′`, and let `m≥3` be the last exceptional position. Choose three rows and columns on
which `D_m` has nonzero determinant. Form the `12 × 12` section

```text
K_(p,i),(q,j) = D_(p+m-q)(i,j),     0≤p,q≤3.
```

Natural subtraction is harmless because `q≤3≤m`. If `q<p`, then `p+m-q>m`, so the corresponding
block is zero. Every diagonal block is the selected `3 × 3` minor of `D_m`. Hence `K` is block
triangular and

```text
det K = det(D_m[selected rows, selected columns])⁴ ≠ 0.
```

The same section factors as

```text
K = LR - xyᵀ,
```

where `L` and `R` factor the transfer moments through the `n` ambient states and `xyᵀ` is the
selected constant tail. Adjoining one coordinate absorbs the rank-one subtraction:

```text
K = [−x  L] [yᵀ; R].
```

Nonsingularity therefore gives `12≤n+1`, hence `n≥11`. This is a rank-one restoration bound;
it does not claim that the difference series itself is a semigroup representation.

For the three benchmark roles, Lean checks the following exact deviation minors:

```text
det((aT-P′)[rows 1,2,3; columns 0,1,3])       = -81 a²,
det((dD_b-P′)[rows 0,2,3; columns 0,1,3])     = 3888 d²,
det((eD_c-P′)[rows 0,2,3; columns 0,1,3])     = 237468348 e².
```

Thus whichever role occurs last supplies the required rank-three deviation.

## Position dichotomy

Three distinct natural-number positions either permute `0,1,2`, or at least one position is at
least three. In the latter case the maximum position is at least three, and the late-exception
argument gives `n≥11`. In the former case `MM-O23` applies: the exact six-order determinant audit
gives `n≥10`. Consequently moving the same three role matrices to sparse, nonconsecutive run
lengths cannot produce a nine-state exact transfer compiler with a constant `P′` tail.

The finite-field position scan used during discovery found the same minimum but is not evidence
for the theorem. The retained proof is unbounded in the run lengths.

## Formal boundary

`MatrixMortality/SparseTransferHankel.lean` checks:

- the generic rank-one restoration bound for a nonsingular square difference section;
- block triangularity and nonsingularity of the four reversed time blocks;
- factorization of that section through one adjoined ambient coordinate;
- the generic implication `m≥3` and selected deviation rank three imply `n≥11`;
- the three exact benchmark deviation determinants;
- the specialized late-toggle, late-data-`b`, and late-data-`c` bounds;
- the exact distinct-position dichotomy and its reduction to either the consecutive case or
  `n≥11`.

The `n≥10` conclusion in the consecutive branch uses the five audited certificates and one
Lean-checked certificate from `MM-O23`. It is therefore an audited assembly rather than a single
Lean theorem. Neither record excludes a history-sensitive same-zero series or a moving safe
tail.
