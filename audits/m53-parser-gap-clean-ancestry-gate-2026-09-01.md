# Parser Gap-Clean Ancestry Gate Audit

**Date:** 2026-09-01
**Target:** integral denominator descent and primitive-gap coprimality for decimal parser rays
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** denominator descent is automatic on the `(1,1)` quotient shell, while gap-clean
descent is equivalent to one exact divisibility condition on the reduced quotient numerator

## Integral Normalization

Let a parser ray be `(x,y)` and write its normalized quotient in lowest terms as

```text
s=(y/x)/10=a/b.
```

On shell `(1,1)`, both `a` and `b` are decimal units. Put `E=9q`, where
`q=2·10^β−7` is the primitive gap, and let `μ` be the decimal marker. The integral coordinates

```text
N=Eμb,       Nprev=a,       D=Ea
```

are decimal units at two and five, satisfy `D=E·Nprev`, and represent the original parser ray.
For one explicit parser step they are a common nonzero rational rescaling of the physical
residual and inherited upper coordinate. Thus the denominator ancestry required by the
recursive carrier arithmetic is automatic once the parser quotient has shell `(1,1)`.

## Exact Clean Gate

Every integral descended representation satisfies the cross identity

```text
aN=bμE·Nprev.                                      (1)
```

The primitive gap is coprime to nine and to the marker. If `gcd(q,N)=1`, equation (1) forces
`q∣a`. Conversely, when `a=q c`, the coordinates

```text
N=9μb,       Nprev=c,       D=Ec=9a
```

are decimal units, represent the ray, and have `gcd(q,N)=1`. Lean therefore proves the exact
equivalence

```text
gap-clean integral descended coordinates exist
  ↔ q divides numerator((y/x)/10).                 (2)
```

Projective rescaling cannot manufacture the coprimality hypothesis in the gap-factor quotient
gate. It is a rigid property of the reduced parser quotient.

## Lawful Obstruction

For every `β≥3` and every tag body, the lawful tail

```text
[R_c,D_c] ; [R_c,R_c]
```

is a uniform obstruction. If `P` is its common punctuated upper code, `V` is the lower code of
the first block, and `G` is the lift, then `P−100μ=−11q` cancels the full gap from the ray
recurrence and gives

```text
(y/x)/10 = 90μP / (9P²−11GV).                     (3)
```

The raw numerator and denominator in (3) are respectively `610` and `990` modulo `1000`, so
both have exact decimal shell `(1,1)` and the ray quotient has shell `(1,1)`. Exact Bézout
identities show that `q` is coprime to the raw numerator, hence also to the reduced numerator.
By (2), no integral gap-clean coordinates exist for this tail at any admissible deletion width
or tag body. Parser law and shell data alone therefore cannot discharge the coprimality premise
of the gap-factor ancestry gate.

## Boundary

The result does not exhibit a singleton pole. The uniform family consists of lawful parser
tails, not reachable mortal witnesses. An actual pole imposes additional code and sign
constraints that may exclude them. Equation (2) isolates the exact missing input: prove the
reduced-numerator divisibility from the pole and encoded-entry history, or analyze the
complementary contaminated support through the factorwise laws.

## Verification

The dedicated module and root aggregate build without warnings. Namespace lint and Lean LSP
diagnostics are clean. The axiom audit is exact; selected declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No proof aperture, external declaration, unsafe definition,
or linter suppression is present.

## Artifacts

- [`DecimalSetterGapCleanAncestry.lean`](../MatrixMortality/DecimalSetterGapCleanAncestry.lean)
- [`DecimalSetterSingletonAncestry.lean`](../MatrixMortality/DecimalSetterSingletonAncestry.lean)
- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s91-exact-parser-gap-clean-ancestry-gate)
