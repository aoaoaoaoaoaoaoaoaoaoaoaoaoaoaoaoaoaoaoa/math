# M₄(3) residue-two wall audit

**Date:** 5 August 2026

**Status:** every residue-{0,1} atom word exterminated; full `M₄(3)` construction still open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide the first open phase of the parabolic blade without enlarging the bridge
infrastructure

## Verdict

The external report's global theorem is correct and strictly strengthens the former closed-phase
wall. Every atom word whose gaps are congruent to zero or one modulo three is nonzero. This
includes every exceptional atom `R=Q(b,1)`, every regular residue-one atom, every closed atom,
arbitrary mixtures, arbitrary length, and the empty word. Therefore every exact zero contains a
gap congruent to two modulo three.

The report also supplied exact 3-adic digits for two shortest residue-two traps, four bilinear
scalar formulas, a body-length bound for one orientation, and a same-zero obstruction for a
one-atom boundary. Independent symbolic reconstruction confirms the displayed lift reductions,
all four bilinear identities, and the `cb` factorization. None classifies arbitrary words after a
residue-two atom occurs, constructs the semantic boundary, or produces an exact malformed zero.
They remain audit coordinates; no Lean API was created for them.

## Checked Cut

Use the canonical alphabet `(x,j,ε)` with `x∈{b,c}` and `ε∈Bool`:

```text
(x,j,false) ↦ Q(x,3j),
(x,j,true)  ↦ Q(x,3j+1).
```

Multiplying each atom by 64 yields an integral matrix. Reduction modulo three is independent of
`x`, `j`, `β`, and the body:

```text
Q₀ = [[1,2,2],       Q₁ = [[0,0,0],
      [0,0,0],             [0,0,0],
      [0,0,0]],            [2,0,2]].
```

On `e₀=(1,0,0)ᵀ` and `e₂=(0,0,1)ᵀ`,

```text
Q₀e₀=e₀,    Q₀e₂=2e₀,
Q₁e₀=2e₂,   Q₁e₂=2e₂.
```

Every residue-{0,1} word therefore sends `e₀` to a nonzero multiple of `e₀` or `e₂`. Its integral
product is nonzero modulo three, hence nonzero over the integers; scalar extension and the
nonzero factor `64ⁿ` transfer nonvanishing to the rational atom product.

Lean proves:

```text
ParabolicBlade.residueTwoWall_wordProduct_ne_zero
  (β : Nat) (body : List TagLetter)
  (word : List (TagLetter × Nat × Bool)) :
  wordProduct (residueTwoWallGenerator β body) word ≠ 0
```

The proof needs no admissibility, lower bound on `β`, nonempty body, or bound on the word.

## Audited Diagnostics

The report's first bridge lift is correct up to one common nonzero unit modulo three. For
`M₀₂=Q(x,3a)Q(y,3b+2)`,

```text
K(M₀₂)/3 ≍ [[b−a, b−a],
             [a−1, a−1]]               mod 3.
```

Thus a second lift is possible only at `a≡b≡1`. Writing `a=1+3a₁`, `b=1+3b₁`, its next digit is

```text
y=b: K(M₀₂)/9 ≍ (b₁−a₁−1, a₁)ᵀ(1,1),
y=c: K(M₀₂)/9 ≍ (b₁−a₁−κ₁−Π, a₁)ᵀ(1,1),
```

where `κ=2+3κ₁` and `Π=3^|tagEncode β body|`. For the opposite orientation,
`σxy(a,b)=vQ(x,3a+2)Q(y,3b)c` satisfies

```text
σby/3 ≍ 1−b,       σcy/3 ≍ 1−b−κ        mod 3.
```

Exact symbolic multiplication also confirms the four reported bilinear formulas for `σbb`,
`σbc`, `σcb`, and `σcc`, including the common factor `Pρ=1026ρ+385`, and confirms

```text
Ncb = QH − 108Z.
```

These calculations distinguish divisibility from equality. They do not prove a bridge zero or
nonzero theorem at arbitrary depth. The report's length bound excludes sufficiently long bodies
only from the shortest `cb` scalar trap for each fixed `β`; longer contexts and the other live
orientations remain.

The semantic identity for `vQ_b(3a+s)Nc` is likewise correct as stated: on the lawful locus
`f(N)=0`, `δ=3ρα`, its remainder is positive for `ρ≥1`, `a,U≥0`, and `α>0`. Its scope fixes the
native right bridge column and a single left `b`-atom. It does not exclude a right context, a
longer left context, or a left `c`-atom, so it does not retire the parabolic family.

## What Was Culled

The former `closedPhaseGenerator`, its special treatment of `R`, and
`closedPhase_wordProduct_ne_zero` were deleted. The stronger residue-two wall uses one canonical
alphabet and one quotient proof, with only five more lines than the narrower module.

The 3-adic state objects, matrix-valuation API, projective-unit relation, four shortest-trap
polynomial families, and semantic remainder decomposition were not formalized. Their only current
consumer would be another local diagnostic. The formulas above preserve the verified attack
coordinates without turning them into permanent supporting machinery.

## Claim Disposition

| Claim | Disposition |
| --- | --- |
| Every residue-{0,1} atom word is nonzero | promotion; strengthened and formalized |
| Every exact zero contains a residue-two gap | checked consequence of the promoted theorem |
| First and second digits of the `Q₀Q₂` trap | audited; culled as unconsumed local structure |
| First digit of the `Q₂Q₀` trap | audited; culled as unconsumed local structure |
| Four exact shortest scalar formulas and `cb` factorization | audited; retained only here |
| Uniform `cb` shortest-trap body-length bound | audited consequence; does not classify longer words |
| One-`b`-atom/native-column semantic obstruction | audited; exact but narrowly scoped |
| Complete open boundary or malformed zero | open |
| `M₄(3)` undecidability | open |

## Exact Wound

```text
MASTER VERDICT: still open
REMOVED: every atom word avoiding residue two, including all regular residue-one boundaries
REMAINS: arbitrary words containing one or more residue-two atoms
DISTANCE: classify the first residue-two atom with arbitrary residue-{0,1} contexts on both
          sides; construct and isolate the paired-Neary boundary, or force an exact malformed zero
```

## Checked Artifacts

- [`MatrixMortality/ParabolicResidueWall.lean`](../MatrixMortality/ParabolicResidueWall.lean)
- `ParabolicBlade.residueTwoWall_wordProduct_ne_zero` in
  [`AxiomAudit.lean`](../AxiomAudit.lean)
- the bridge contraction in
  [`MatrixMortality/ParabolicBlade.lean`](../MatrixMortality/ParabolicBlade.lean)

The external transcript, report, symbolic reconstruction scripts, enemy lock, and next prompt
remain transient under `/tmp`.
