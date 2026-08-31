# M₃(4) Whole-Carrier Row Obstruction Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `153cfbd` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseInfiniteAtlas.lean`](../MatrixMortality/TransverseInfiniteAtlas.lean)

## Verdict

A nonzero rational terminal row can annihilate at most one whole plane in the injectively infinite
carrier orbit of `G3-O30`. The nonprojective toggle depth therefore cannot encode an unbounded
terminal set merely by declaring selected carrier planes entirely terminal.

This is a terminal-row narrowing, not a no-go for the infinite-carrier architecture. Proper line
intersections survive at every other depth.

## Exact Equations

Recall

```text
C_n(s) = im(TⁿD_s),

v_n = (1,−2ⁿ,0),          w_n(s) = (s,0,−3ⁿ).
```

Both displayed vectors belong to `C_n(s)` and span it. Let `λ=(a,b,c)`. If `λ` annihilates the
whole planes at depths `n<m`, evaluating the first vector at both depths gives

```text
a−b2ⁿ=0,                 a−b2ᵐ=0.
```

Since `2ⁿ<2ᵐ`, subtraction forces `b=0`, then `a=0`. Evaluating the second vector at depth `n`
gives

```text
as−c3ⁿ=0.
```

The first term is now zero and `3ⁿ≠0`, so `c=0`. Thus `λ=0`. No condition on `s` enters the
argument.

## Formal Statement

The Lean predicate

```text
AnnihilatesCarrier λ s n
```

means that `λ` vanishes on every member of the actual submodule `C_n(s)`. Lean proves

```text
n<m ∧ AnnihilatesCarrier λ s n ∧ AnnihilatesCarrier λ s m  ⇒  λ=0.
```

It then removes the ordering by trichotomy and packages the operational conclusion as

```text
λ≠0  ⇒  Set.Subsingleton {n | AnnihilatesCarrier λ s n}.
```

The theorem quantifies over every rational row, source parameter, and pair of depths.

## Boundary Of The Cut

For a nonzero row and a depth at which the entire carrier is not annihilated, the section

```text
C_n(s) ∩ ker λ
```

is a vector line or the zero subspace. The present theorem does not compare these moving lines,
decide their point reachability, or rule out encoding terminal arithmetic in their projective
coordinates. It also fixes the `G3-O30` matrices; source-dependent controls outside that family
remain open.

A surviving construction must now provide all three of the following:

1. a source-computable row or broader boundary;
2. an exact arithmetic description of the proper line sections over unbounded toggle depths;
3. a converse excluding every malformed raw word.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Both spanning witnesses belong to each actual carrier submodule | promotion | Lean theorems `witness_mem_carrier`, `sourceWitness_mem_carrier` |
| Whole-plane vanishing at two ordered depths forces the row to zero | promotion | Lean theorem `row_eq_zero_of_annihilates_two` |
| A nonzero row has at most one whole-carrier depth | promotion | Lean theorems `annihilatesCarrier_at_most_one`, `wholeCarrierDepths_subsingleton` |
| All proper line sections are decidable | rejected | their arithmetic is not analyzed here |
| Source-dependent terminal rows are impossible | rejected | the theorem is pointwise in the arbitrary row and source parameter |
| The nonprojective architecture is closed | rejected | moving line sections remain live |
| `M₃(4)` follows | rejected | no paired recognizer is constructed |

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: accepting an unbounded set of G3-O30 depths by whole-plane annihilation under one
         nonzero row.
REDUCED: the live terminal geometry to proper moving line sections at all but at most one depth.
SURVIVOR: solve or exploit that line arithmetic with a complete raw-word converse.
```

