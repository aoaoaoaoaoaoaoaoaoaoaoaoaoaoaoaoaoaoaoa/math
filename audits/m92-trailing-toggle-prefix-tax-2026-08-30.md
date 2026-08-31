# The trailing-toggle boundary and the exact prefix tax

**Date:** 2026-08-30  
**Target:** `M₉(2)`  
**Verdict:** one source-independent boundary move reaches an exact ten-state throat; every
direct-sum exact binary prefix realization of the resulting four roles still needs at least ten
states. The surviving seam is a non-exact, history-sensitive same-zero compiler.

## Scope before calculation

The obstruction proved here assumes all of the following.

1. Four source roles are assigned injectively to the leaves of a complete binary prefix tree.
2. The physical state space is the direct sum of one fibre for every proper prefix.
3. Each source role is the exact product of the edge maps on its root-to-leaf path. There are no
   cross-path sums, shared coordinates between fibres, or state-dependent changes of value.
4. One role has rank four and two roles have rank three.

These hypotheses do **not** include invertibility of every ordinary role, a common-image quotient,
or the factorized face equations used by the earlier cross-ratio obstruction. In particular, the
rank-one separator and the two singular data roles are allowed. Conversely, this audit says
nothing about a compiler which preserves only existence of a zero, overlaps parser fibres, or
uses malformed histories to change all nonzero values.

## Exact boundary absorption

Let `T` be the four-state paired toggle, `C` the paired terminal column, `L` the coefficient row,
and

```text
f(w) = L A_w C.
```

The toggle is an involution: `T²=I`. Define the absorbed column and shifted series by

```text
C′ = TC,                 g(w) = L A_w C′ = f(wt).
```

For every control word `w`, independently of the source body,

```text
f(wtt)=f(w).
```

It follows in both directions that

```text
∃ nonempty w, g(w)=0    ↔    ∃ nonempty w, f(w)=0.
```

The forward map appends one toggle to a zero of `g`; the reverse map also appends one toggle,
then cancels the resulting two-toggle suffix. This proof uses neither a terminal-word grammar nor
universal nonvanishing of malformed words.

In paired coordinates the original column is `(m,−1,3^(β+1),0)ᵀ`, so

```text
C′=(m,0,3^(β+1),−1)ᵀ.
```

Thus `C′` lies in the plane

```text
H={x∈ℚ⁴ : x₁=0}.
```

Both paired data generators have every image in `H`, and the absorbed separator `P′=C′L` does
too. The toggle has rank four; each data generator has rank three. All of these statements are
Lean-checked.

## Prefix tax

Suppose a depth-three leaf has exact factorization

```text
D = E₁E₂E₃
```

through root, middle, and deep fibres. If `rank(D)=3`, the rank inequalities for a product force
both intermediate fibres to have dimension at least three. A rank-four short leaf forces the
root fibre to have dimension at least four. Hence a comb whose short leaf is the toggle costs

```text
4+3+3=10.
```

This is the best placement. A complete four-leaf binary tree is either balanced or a comb.

- In the balanced tree, the toggle branch costs `4+4`; the opposite branch contains a rank-three
  data role and costs another `3`, for at least eleven states.
- In the comb, placing the toggle at depth two costs at least `4+4+3=11`; placing it at depth
  three costs at least twelve. If the toggle is the short leaf, the two deepest leaves include a
  rank-three data role, giving the sharp lower bound ten.

The formal theorem is stated at the matrix-factor level. The two tree-shape observations above
identify its hypotheses in every exact four-leaf prefix layout.

## Exact finite diagnostics

Exact rational calculations at `β=3`, body `bb`, were used only to falsify candidate layouts.
The census, including the absence of a nine-state layout in this enumerated implementation
class, is computational only and is not part of the unbounded rank theorem.

For both complete tree shapes, all 24 assignments of `T,P′,D_b,D_c` were factored through bases
of the accumulated leaf images. Every balanced assignment used eleven states. In the comb,
exactly six assignments used ten states: precisely those with `T` as the short leaf and the other
three roles in arbitrary order. The other comb assignments used eleven or twelve states.

One representative uses codes

```text
0 ↦ T,       10 ↦ P′,       110 ↦ D_b,       111 ↦ D_c.
```

Let `J : ℚ³ → H` insert coordinates `0,2,3`, and put `Q=Jᵀ`. On
`ℚ⁴⊕ℚ³⊕ℚ³`, define the nonzero blocks

```text
B₀[root,root]=T,          B₀[middle,root]=QP′,
B₀[deep,root]=QD_b,

B₁[root,middle]=J,        B₁[middle,deep]=I₃,
B₁[deep,root]=QD_c.
```

The four displayed code products have the required root corner exactly, and the joint image of
`B₀,B₁` has dimension ten. The word `010` is rank one. For every nonzero word through length
nine, its reachable/observable internal sandwich had exact dimension ten. Replacing `L` by each
distinct row `LA_q` with `|q|≤4` also left that sandwich dimension ten. These bounded checks make
simple boundary-orbit repair implausible; they do not prove full-algebra saturation or exclude a
different ten-state pair.

## Consequence for `M₉(2)`

Trailing-toggle absorption is a genuine changed-source move outside the factorized cross-ratio
face. It saves one state over the unshifted variable-fibre comb, but the exact rank profile spends
the saving immediately and stops at ten.

Reordering codes, transposing the roles, moving the coefficient row through a bounded source
orbit, or taking another exact factor basis cannot by itself justify nine states. A live attack
must violate at least one stated hypothesis: overlap parser fibres, admit cross-path
superposition, preserve only the existential zero predicate, or replace the paired source.

## Artifacts

- Lean: `MatrixMortality/PairedBinaryPrefixTax.lean`.
- Registry: `MM-O19`.
- Checked declarations include `pairedProduct_append_toggle_toggle`,
  `pairedTrailingToggle_hasNonemptyZero_iff`,
  `VariablePrefixRankTax.ten_le_of_rank_four_short_rank_three_deep`, and
  `VariablePrefixRankTax.eleven_le_balanced_rank_four_rank_three`.
