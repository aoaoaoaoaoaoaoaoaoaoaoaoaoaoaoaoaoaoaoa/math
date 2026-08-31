# M₃(2) ReturnSquare Proper-Rest Pivot Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S52` bounds a pure-denominator word only when one denominator prime is deeper than the
complete adjugate tail. A word can cross that shell by acquiring common denominator content.
This audit moves the depth comparison to the proper rest and isolates the exact first-letter
divisor created by the crossing.

## Middle Shell

Let `tail=first::rest`, `E′=waitExponent(rest)`, `E=first+1+E′`,
`r=vₚ(q)>0`, and `a=vₚ(B)`. In the middle chamber

```text
2E′r<a≤2Er,
```

the upper adjugate coordinate has exact valuation `a+2E′r`. The lower coordinate is nonzero and
has valuation at least `a`. Therefore an incidence `R=qʰS` forces `h≤2E′`. Together with
`2E′r<a`, this bounds both the proper-rest weight and the source exponent.

## First-Letter Divisor

For the fixed rest state `(U,V)`, put `t=q^(first+1)` and `s=qʰ`. Direct expansion of the first
adjugate letter gives

```text
t ∣ B(s−1)V.
```

Because `t` and `s−1` are coprime, Lean proves `t∣BV`. Every adjugate letter is invertible over
the rationals when `q≥2` and `B≠0,1`, so `(U,V)≠(0,0)`. If `V=0`, the incidence cancels the
nonzero factor `tU` and yields `B=s`, the one-return resonance. Otherwise `BV` is nonzero and
has finitely many power-of-`q` divisors, bounding `first`.

## Pivot

Assume only `2E′r<a`. If `2Er<a`, `R32-S52` supplies the deep synchronization and bounds. If
`a≤2Er`, the middle-shell head bound and first-letter divisor apply. Thus every physical bridge
with one proper-rest-deep prime is a finite exact search, apart from a parameter already known
to be resonant.

## Scope

The pivot requires integral `q≥2`, pure denominator `B≠0,1`, and one prime satisfying
`2E′vₚ(q)<vₚ(B)`. The remaining chamber satisfies the reverse inequality at every denominator
prime. There `B∣q^(2E′)`, so both coordinates of the proper-rest state share `B`; the next proof
must iterate or obstruct that common-content cancellation.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| crossing the complete-tail shell leaves an unbounded first wait | rejected | the first scale divides fixed `BV` |
| `V=0` defeats the divisor bound | rejected | nonvanishing forces the one-return resonance |
| a proper-rest-deep prime leaves an infinite bridge family | rejected | both depth chambers are finite |
| arbitrary-composite ReturnSquare is classified | open | iterated proper-rest common content remains |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every proper-rest-deep pure-denominator branch is finite

EXACT THROAT: iterate the common factor `B` through a simultaneously shallow proper rest

## Evidence

The formal owner is
[`ReturnSquarePureDenominator.lean`](../MatrixMortality/ReturnSquarePureDenominator.lean). The
focused module build, umbrella build, transitive axiom inspection, Lean LSP diagnostics,
forbidden-aperture scan, and whitespace gate passed at the recorded commit.
