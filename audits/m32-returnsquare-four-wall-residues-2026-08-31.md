# M₃(2) ReturnSquare Four-Wall Residue Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S46` leaves four valuation ties in the inverse fraction recurrence. The audit determines
their exact common-content coordinates and whether any tie alone forces a one-return resonance.

## Exact Coordinates

For `d=A/B`, the affine inverse branch is

```text
F_t⁻¹(s)=B(st−A)/(st+(B−A)t²−B).                            (1)
```

Fix a prime dividing `B`, with `A` a unit, and write

```text
a=vₚ(B)>0,      b=vₚ(t)>0,      x=vₚ(s).
```

Lean checks the following complete normal forms.

| Wall | Normalized coordinate | Exact transition |
|---|---|---|
| `x=−b` | `st−A` | denominator unit; `vₚ(F_t⁻¹(s))=a+vₚ(st−A)`; zero iff `st=A` |
| `x=b`, `s=tu` | `η=t²(u+B−A)/B−1` | `F_t⁻¹(tu)=(t²u−A)/η`; numerator unit, so output depth is `−vₚ(η)` |
| `x=a−b`, `st=Bu` | `θ=u−1+(B−A)t²/B` | `F_t⁻¹(s)=(Bu−A)/θ`; numerator unit, so output depth is `−vₚ(θ)` |
| `a=2b` | `κ=(B−A)t²/B−1` | `vₚ(κ)≥0` when nonzero and `F_t⁻¹(s)=(st−A)/(st/B+κ)` |

The equal-scale first residue `u+B−A` yields the exact unequal-shell minimum before normalization;
if it vanishes, the predecessor is the unit `A−t²u`. The denominator-scale center `u=1` yields
the exact monomial transition `B/t²`. On the critical wall with `y=vₚ(st)>0`, the sole secondary
tie is `y−a=vₚ(κ)`; away from it the predecessor depth is
`−min(y−a,vₚ(κ))`.

No primitive vector is chosen in these calculations. Each common `B` is canceled by equality in
`ℚ`; the surviving residue retains every further common factor.

## Wall Fracture

Lean checks

```text
d=3/4,      scales=[44,2,6,10,6]
```

as a nonresonant normalized bridge zero. Every scale is even. Its reverse inverse orbit is

```text
4 ─6→ 3/2 ─10→ 16/37 ─6→ −3/64 ─2→ 132=3·44.              (2)
```

At the prime two, the first step in (2) has `a=2b`; the second target has
`x=v₂(3/2)=−1=−v₂(10)`. Thus one exact multi-return zero crosses both the critical and numerator
walls while every scale shares the denominator prime. The earlier arbitrary-scale fractures
cross the equal-scale and target-scale-versus-denominator walls. None of the four local walls
forces resonance.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| each of the four walls has one exact residue coordinate | promoted | algebraic identities and p-adic shell theorems checked |
| the critical residue is nonnegative | promoted | both terms before normalization are units at `a=2b` |
| `st=B` is a residue-sensitive branch | rejected | it collapses exactly to `B/t²` |
| any one wall forces a one-return resonance | rejected | exact even-scale multi-return fracture plus earlier wall examples |
| a shared denominator prime forces resonance | rejected | every scale in (2) is even |
| common powers of one base force resonance | open | (2) is not a geometric-power word |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every valuation tie is reduced to one exact normalized rational residue

EXACT THROAT: exploit the common-geometric relation among successive residues; local valuations,
individual wall exclusions, divisibility order, and common prime content are all insufficient

## Evidence

The formal owner is
[`ReturnSquareFractionPullback.lean`](../MatrixMortality/ReturnSquareFractionPullback.lean).
The focused module build, default namespace linters, transitive axiom inspection, Lean LSP
diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
