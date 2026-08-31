# Fixed Symmetric-Square Leakage Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `0dcf639` on `wave3-m34-ucb`

**Salvage record:** `G3-S05`

## Verdict

A fixed full-rank insertion cannot reconcile an irreducible symmetric-square orbit with the
line-or-plane complete-fork carrier from `G3-S03`. If three distinct binary rays become dependent
after fixed leakage between nonsingular binary coordinate changes, the leakage is singular.

## Exact Cut

For binary matrices `P,Q`, a `3×3` matrix `L`, and three pairs `u,v,w`, Lean proves over every
commutative ring

```text
det(Sym²(P)L Sym²(Q)[ν(u) ν(v) ν(w)])
  = det(P)³ det(L) det(Q)³ Δ(u,v)Δ(u,w)Δ(v,w).
```

Over a commutative domain, if `P,Q,L` are nonsingular and all three cross determinants are
nonzero, the transported columns have nonzero determinant. The checked contrapositive states the exact carrier seam: under
nonsingular `P,Q` and three pairwise-distinct rays, a zero transported determinant forces
`det(L)=0`.

The `G3-S03` carrier theorem supplies that zero determinant whenever three accepted
complete-fork states lie in its forced subspace of dimension at most two. Therefore a fixed
nonsingular leakage does not rescue direct non-elementary Sym² fork blocks. Any surviving fixed
insertion loses rank and must explain how the erased direction is recovered without adding a
state.

## Boundary

The theorem does not cover singular leakage, a leakage map chosen from the word or source
instance, or an orbit with at most two binary rays. Nor does singularity alone imply elementary
dynamics: a rank-two insertion may still encode useful transient information. Malformed-control
policing and arbitrary-product mortality remain separate obligations.

## Verification

```text
lake build MatrixMortality.SymmetricSquareCollision
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

The publication theorems are listed in `AxiomAudit.lean` and the reviewed snapshot. No project
axiom, proof aperture, linter suppression, or reference file was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Binary pre/post changes and fixed leakage obey the displayed determinant transport | promotion | Lean-checked determinant multiplicativity |
| Full-rank fixed leakage preserves independence of three distinct Veronese rays | promotion | Lean-checked nonzero-factor theorem |
| A planar image of three distinct rays forces fixed leakage singular | promotion | Lean-checked contrapositive |
| Full-rank fixed leakage repairs the direct Sym² complete fork | rejected | `G3-S03` carrier dependence plus this cut |
| Singular or dynamically varying leakage is impossible | open | outside the hypotheses |
| `M₃(4)` or `M₂(3)` is decided | open | no syntax or reachability converse follows |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: full-rank fixed leakage around direct Sym² complete-fork dynamics.
REMAINS: singular leakage with explicit recovery, or genuinely word/source-
         dependent insertion; all raw-control and reachability obligations.
```

## Artifacts

- [`SymmetricSquareCollision.lean`](../MatrixMortality/SymmetricSquareCollision.lean)
- [`G3-S05`](../SALVAGE.md#g3-s05-fixed-full-rank-symmetric-square-leakage-no-go)
