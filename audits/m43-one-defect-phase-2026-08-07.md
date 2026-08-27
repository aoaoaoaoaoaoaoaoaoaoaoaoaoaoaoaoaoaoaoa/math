# M₄(3) one-defect phase audit

**Date:** 7 August 2026

**Status:** one-defect words reduced to two alternating phases; `M₄(3)` remains open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** classify one residue-two atom under arbitrary residue-{0,1} contexts

## Verdict

The external report contains no reduction, malformed zero, safe-return theorem, or complete
one-defect decision. Its exact modulo-three calculation does remove two of the four internal
adjacency phases at arbitrary context length. A one-defect word is nonzero if either safe side is
empty or if the adjacent safe atoms have the same residue. Only `0|2|1` and `1|2|0` remain.

The same-residue case is now kernel-checked. The edge cases already follow from two existing
theorems: every safe word is nonzero, and every residue-two atom is invertible. No duplicate edge
API was added.

The report's five-atom calculation

```text
R² Q(b,3j+2) R² ≠ 0
```

is correct but is exactly the `1|2|1` instance of the general phase theorem. It was culled.

## Source Lock

The share records a 10,778-byte Markdown attachment, matching the local prompt length. The final
answer reproduces prompt ID `M43-RESIDUE-ONE-SKELETON-v3` and source commit
`0eb9bf6449f5e5345f7cf964b7c8d16ad4922d20`. The local prompt digest is
`b895578861f0765014e2d8e639c6d85c7d20fb676179c6f8f5a55cc32fa56b4c`.

## Checked Cut

Multiplication by 64 clears every atom integrally. Reduction modulo three depends only on the gap
residue:

```text
Q₀ = [[1,2,2],    Q₁ = [[0,0,0],    Q₂ = [[1,0,1],
      [0,0,0],          [0,0,0],          [0,0,0],
      [0,0,0]],         [2,0,2]],         [2,1,1]].
```

On `span(e₀,e₂)`, write

```text
A₀ = p₀q₀ᵀ = [[1,2], [0,0]],
A₁ = p₁q₁ᵀ = [[0,0], [2,2]],
A₂            = [[1,1], [2,1]].
```

Every safe transition weight is nonzero. Consequently a nonempty safe product has column ray
fixed by its leftmost residue and row ray fixed by its rightmost residue. For safe contexts `U,V`
and one defect `D=Q(x,3j+2)`, the only new scalar is determined by the atoms adjacent to `D`:

```text
phaseTable(i,k) = qᵢᵀ A₂ pₖ = [[2,0],
                                 [0,1]].
```

The diagonal phases are nonzero. The off-diagonal phases vanish modulo three and therefore need
an exact lift; no zero is implied.

Lean proves:

```text
ParabolicBlade.oneDefect_wordProduct_ne_zero_of_same_residue
  (sameResidue : leftAdjacent.2.2 = rightAdjacent.2.2) :
  wordProduct Qsafe (leftPrefix ++ [leftAdjacent]) *
      Q(defectLetter, 3 * defectWait + 2) *
    wordProduct Qsafe (rightAdjacent :: rightSuffix) ≠ 0
```

The theorem quantifies over arbitrary `β`, body, letters, waits, and context lengths, including
arbitrarily many exceptional atoms.

## Independent Reconstruction

The integral residue-two formulas were derived from the repository definitions of `bAtom`,
`cAtom`, and `normalRoot`; their casts equal 64 times the rational atoms entrywise. The phase
action was then proved by the existing safe-ray automaton, not accepted from the report.

The reported four-exceptional scalar also reconstructs exactly. With the pinned blade rays,

```text
row(ρ) Q(b,3j+2) column(ρ)
 = 144(4ρ+1)(1026ρ+385)j
   -174960ρ³+477576ρ²+347457ρ+56770
 ≡ 1 mod 3.
```

This confirms the calculation but adds nothing after the arbitrary-context theorem.

## Disposition

| Claim | Disposition |
| --- | --- |
| Safe products are nonzero rank one modulo three | correct; already owned by `M4-O08` |
| Same-residue one-defect words are nonzero | formalized as `M4-S03` |
| Empty-side one-defect words are nonzero | checked consequence; no new API |
| `R² Q(b,3j+2) R² ≠ 0` | correct instance of `M4-S03`; culled |
| Alternating phases vanish after the first reduction | correct; divisibility only |
| Safe return, complete one-defect nonvanishing, or `M₄(3)` | open |

## Exact Wound

```text
MASTER VERDICT: still open
REMOVED: one-defect words with an empty safe side or local phase 0|2|0 or 1|2|1
REMAINS: one-defect phases 0|2|1 and 1|2|0 under arbitrary safe contexts; then successive
         residue-two defects
DISTANCE: lift the two alternating phases exactly, using a global invariant or an exact return;
          consume the result in arbitrary bridge products and the paired-Neary boundary
```

## Checked Artifacts

- [`MatrixMortality/ParabolicResidueWall.lean`](../MatrixMortality/ParabolicResidueWall.lean)
- `ParabolicBlade.oneDefect_wordProduct_ne_zero_of_same_residue` in
  [`AxiomAudit.lean`](../AxiomAudit.lean)

The shared transcript, report, source HTML, enemy lock, symbolic checks, and next prompt remain
transient under `/tmp`.
