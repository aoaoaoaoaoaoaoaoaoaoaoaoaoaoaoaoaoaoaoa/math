# M₃(2) ReturnSquare Finite-Decision Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S51` makes every positive-numerator tail finite at one positive base-prime valuation, and
`R32-S54` makes every pure-denominator word finite. Neither statement alone is a decision
procedure: the head search, support failures, numerator-one seam, and parameter `-1` still need
one exact assembly.

## Computable Word Boxes

The module defines a recursive `Finset` enumerator for all natural-number lists shorter than a
given bound with every entry below that bound. Its membership theorem is exact, and the
definition contains no classical or noncomputable dependency.

For `d=1/B`, `B>1`, global descent puts every zero in the box

```text
length<B,       every wait<B.
```

Filtering this box by rational bridge equality produces a finite set whose nonemptiness is
equivalent to physical mortality.

## Positive Numerators

Let `d=A/B` be reduced with `A>1`, and choose `p=minFac(A)`. Coprimality proves `vₚ(d)>0`.
If `p∤q`, canonical numerator support rejects every zero. If `p∣q`, every zero has a nonempty
proper tail and one weight `W` satisfying

```text
waitExponent(tail)=W,       vₚ(d)=Wvₚ(q).
```

The candidate generator enumerates `1≤W≤vₚ(d)` and filters by this equation. For each surviving
weight it enumerates all tails of that weight.

The general integral adjugate tail state is proved nonzero by invertibility of every rational
adjugate letter. If its coordinates are `(R,S)`, a separated-head zero gives

```text
R=Aq^(head+1)S.
```

Consequently `R,S≠0`, `q^(head+1)∣R`, and `head<|R|`. The exact computed `|R|` is a finite head
bound for that tail. Exact bridge evaluation filters the resulting word set.

## Seams

For `A=B=1`, reducedness identifies `d=1`; the module invokes the zero-power resonance directly.
For `A=1<B`, it invokes the pure-denominator box. For `A>1`, it follows the support/valuation
split above. These branches construct

```text
Decidable (IsMortal (ReturnSquare(q,−A/B)))
```

for every `q≥4`, `A,B>0`, and `gcd(A,B)=1`. This covers every composite integral base. Small
prime bases already have the stronger resonance-only theorem.

## Executability

The candidate generators and final `Decidable` term are computational definitions. A direct
Lean evaluation returns one candidate for `(q,B)=(4,4)`, namely the one-return resonance, and no
candidate for the checked positive-numerator instance `(q,A,B,p)=(6,2,3,2)`.

The present enumerator uses transparent rectangular supersets. The sharper additive cost bound
can prune large pure-denominator searches, but this is a performance refinement, not a logical
gap.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| the pure-denominator bound still leaves an infinite word search | rejected | all words lie in one recursive finite box |
| the positive-numerator head remains unbounded | rejected | it is smaller than the exact upper adjugate coordinate's absolute value |
| a numerator prime outside the base needs a search | rejected | rational-root support excludes every bridge |
| the parameter `-1` falls through the generic bridge equivalence | rejected | it is handled directly as the zero-power resonance |
| ReturnSquare remains undecided at composite bases | rejected | Lean constructs a uniform `Decidable` term |
| every composite-base mortal parameter is resonant | open | the decision set may contain bounded nonresonant roots |

MASTER VERDICT: ReturnSquare is decidable for every integral base at least two

NEW WOUND: the arbitrary-composite decision frontier is closed

EXACT NEXT STEP: execute or contract the finite sets to settle resonance-only classification

## Evidence

The formal owner is
[`ReturnSquareFiniteCertificate.lean`](../MatrixMortality/ReturnSquareFiniteCertificate.lean).
The focused module build, umbrella build, transitive axiom inspection, Lean LSP diagnostics,
forbidden-aperture scan, whitespace gate, and direct candidate evaluation passed at the recorded
commit.
