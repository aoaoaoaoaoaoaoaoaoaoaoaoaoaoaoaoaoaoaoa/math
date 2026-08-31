# M₃(2) ReturnSquare Denominator-Shell Grammar Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S45` computes the final inverse step from the terminal line. A complete denominator attack
must iterate that pullback and explain whether a unit or negative predecessor can later regain
positive denominator depth.

## Arbitrary Inverse Branch

For `d=A/B`, let

```text
H_t = [(B−A)t²−B   AB].
      [−t            Bt]
```

The homogeneous predecessor of an arbitrary target ray `(s,1)` is

```text
[B(st−A), st+(B−A)t²−B].                                    (1)
```

Lean proves that applying `H_t` to (1) gives
`B(B−A)t(t²−1)(s,1)`. It also proves the cross-multiplied converse, so off the displayed pole
the affine predecessor is uniquely

```text
F_t⁻¹(s)=B(st−A)/(st+(B−A)t²−B).                             (2)
```

## Tropical Grammar

Fix a prime dividing `B`. Reducedness makes `A` a unit. Write

```text
a=vₚ(B)>0,      b=vₚ(t)>0,      x=vₚ(s).
```

If `x+b<0`, then `st` dominates the unit `A` in the numerator and both positive-valuation terms
in the denominator. Their shared `x+b` cancels in the quotient, leaving

```text
vₚ(F_t⁻¹(s))=a.                                              (3)
```

If `x+b>0`, then `st−A` is a unit. The three denominator terms have valuations
`x+b`, `2b`, and `a`. When pairwise distinct, the least survives:

```text
vₚ(F_t⁻¹(s))=a−min(x+b,2b,a).                                (4)
```

Equations (3)–(4) leave exactly four equality walls:

```text
x=−b,          x=b,          x=a−b,          a=2b.           (5)
```

The first is cancellation in `st−A`; the others are the three pairwise ties in the denominator.
At one-base scales, `b=(w+1)vₚ(q)`, so (5) is a finite word-visible branch set at every inverse
step.

## Consequences

Negative depth can re-enter: the regime `x<−b` resets to the full depth `a`. Unit depth can also
re-enter when `a>b`, since the tie-free formula gives `a−b`. Thus neither “once drained, always
drained” nor monotone inverse depth is lawful. Conversely, no free valuation choice survives
away from (5): the update is deterministic and piecewise linear.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| every target has the inverse branch (2) | promoted | homogeneous image and cross-multiplied uniqueness checked |
| negative targets below `−b` reset to depth `a` | promoted | exact unequal-shell calculation checked |
| positive-side tie-free dynamics obey (4) | promoted | all three denominator terms retained and checked |
| drained denominator depth is forward invariant under inverse search | rejected | (3) and the unit case explicitly permit re-entry |
| only four valuation walls remain locally | promoted | exhaustive equalities among numerator and denominator shell terms |
| wall residues synchronize across primes | open | different primes may hit different equalities and share reduction content |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: all denominator-prime inverse dynamics outside four explicit moving walls is deterministic

EXACT THROAT: classify residue and common-content transitions on `x=−b`, `x=b`, `x=a−b`, and `a=2b`, then enforce the boundary path from `B` to `At_head`

## Subsequent Disposition

[`R32-S47`](../SALVAGE.md#r32-s47-exact-four-wall-residue-laws) supplies exact normalized
coordinates for all four walls and rejects every wall as a standalone resonance obstruction.
The surviving throat is global compatibility under scales that are powers of one common base.

## Evidence

The formal owner is
[`ReturnSquareFractionPullback.lean`](../MatrixMortality/ReturnSquareFractionPullback.lean).
The focused module build, default namespace linters, transitive axiom inspection, Lean LSP
diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
