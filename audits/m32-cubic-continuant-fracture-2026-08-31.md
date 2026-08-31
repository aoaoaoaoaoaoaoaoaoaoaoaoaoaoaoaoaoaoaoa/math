# M₃(2) Cubic Continuant Fracture Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The scalar flag defect of the false-wait cubic family vanishes exactly at waits
`0,1,5,14`. This classifies single upper-triangular returns but does not control products whose
nonzero lower-left entries cancel. The remaining local question was whether such cancellation
requires the seven-letter endpoint witness already known, or whether it begins inside a smaller
matrix-product block.

It begins at length three. Two exact words consist entirely of nontriangular returns, have no
triangular adjacent pair, and nevertheless multiply to upper-triangular matrices. The full
return family also admits a recurrence-state Bruhat form, so arbitrary cancellation is now one
generalized continuant problem rather than an unspecified interaction among four matrix entries.

## State Projection

Write

```text
(a,b,c)=(uₙ,uₙ₊₁,uₙ₊₂),       uₙ₊₃=uₙ−uₙ₊₂.
```

Lean proves the complete return identity

```text
Mₙ = [[−63a+24b, 24a−21b−79c],
      [−90a,     −30b−90c     ]],                         (1)
```

not merely its lower-left projection. Its determinant is

```text
det Mₙ=720(3a²−2ac−b²−3bc).                              (2)
```

For `n>0`, the prior trace audit proves that (2) is positive. When `a≠0`, put

```text
xₙ = 7/10−4b/(15a),
yₙ = (b+3c)/(3a),
tₙ = 4(3a²−2ac−b²−3bc)/(45a²).
```

In the affine coordinate `z=X/Y`, direct division of (1) gives

```text
Mₙ(z)=xₙ−tₙ/(z+yₙ).                                     (3)
```

Equation (3) is the Bruhat normal form
`[[A,B],[C,D]]z=A/C−det(M)/(C²(z+D/C))`. A word of nontriangular returns is
therefore a negative generalized continued fraction in recurrence-state digits. A product is
upper triangular exactly when its evaluation at `∞` returns to `∞`. The positive triangular
waits `1,5,14` act as affine letters and can be absorbed at continuant boundaries.

## Ternary Fractures

For waits `8,15,26`, the relevant digits are

```text
(x₈,y₈,t₈)=(5/6,−2/3,4/15),
x₂₆=4/5,       y₁₅=7/6.
```

Hence

```text
M₂₆(∞)=4/5,
M₈(4/5)=5/6−(4/15)/(4/5−2/3)=−7/6,
M₁₅(−7/6)=∞.
```

Lean checks that all three lower-left entries and both adjacent-pair lower-left entries are
nonzero, while

```text
M₁₅M₈M₂₆ = [[9331200,71139600],[0,85665600]].            (4)
```

The second fracture uses

```text
x₃₃=118/105,
M₈(118/105)=5/6−(4/15)/(118/105−2/3)=1/4,
y₁₂=−1/4,
```

and Lean proves

```text
M₁₂M₈M₃₃ = [[−32348160,−70752420],[0,−76663800]].        (5)
```

Again every letter and adjacent pair is nontriangular. Equations (4) and (5) are genuine
upper-triangular macro letters assembled from the nontriangular alphabet; they do not reach the
singular endpoint by themselves.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| all four return entries are one linear projection of the defect window | promotion | Lean-checked identity (1) |
| determinant is the quadratic companion (2) | promotion | Lean checked |
| nontriangular words have the continuant form (3) | promotion | exact Bruhat identity applied to (1) |
| factorwise nonzero defects prevent product cancellation | rejected | (4) and (5) |
| checking every adjacent pair prevents longer cancellation | rejected | both adjacent pairs in each fracture remain nontriangular |
| the two displayed triples classify all ternary cancellation | open | no completeness claim or finite search is retained |
| the continuant language is decidable | open | independently selected recurrence indices still give unbounded depth |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: factorwise defect avoidance; adjacent-pair triangularity as an all-word guard; a four-entry description of cancellation
EXACT CUBIC THROAT: endpoint reachability for the recurrence-digit generalized continuant, with affine waits {1,5,14} and derived triangular macro words
NEXT: find descent or a decision grammar for this continuant language, or exploit its ternary fractures as controlled punctuation in a sound compiler
```
