# M₃(2) ReturnSquare Divisibility-Chain Fracture Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The prime-power ReturnSquare theorem relies on all positive-return scales being powers of one
base. A proposed extension replaced that geometric condition by a weaker order condition: the
scale alphabet is totally ordered under divisibility. This audit tests that exact hypothesis.

## Certificate

Let

```text
s = [3,15,3,3,15,3,3,3],             d = 25/27.
```

Lean checks all three parts of one certificate:

```text
Pairwise (fun u v => u∣v or v∣u) s,
(wordProduct (normalizedTransfer d) s)₀₀ = 0,
for every t in s, d ≠ t⁻¹.
```

The first line is a full pairwise statement, not merely the isolated fact `3∣15`. The second
line uses the project's canonical list-product orientation and normalized ReturnSquare matrix.
The third line excludes both one-return resonances.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the two-scale alphabet is totally ordered by divisibility | promotion | Lean checked pairwise on the whole word |
| the displayed word has a rational bridge zero | promotion | Lean checked exactly over `ℚ` |
| the zero is a one-return resonance | rejected | `25/27` is neither `1/3` nor `1/15` |
| divisibility-chain scales force resonance-only roots | rejected | contradicted by the certificate |
| arbitrary-composite ReturnSquare has a nonresonant zero | not implied | `3` and `15` are not powers of one base |

## Boundary

The counterexample kills the divisibility-chain generalization, not the one-base geometric
problem. Any arbitrary-composite ReturnSquare proof may use more than pairwise divisibility: it
must exploit the exact shared exponent map `t=qⁿ`. The negative-valuation branch in
[`R32-S44`](../SALVAGE.md#r32-s44-composite-returnsquare-tail-synchronization) remains open.

## Validation

The certificate is `ReturnSquare.divisibilityChain_twentyFive_twentySeven_zero` in
[`ReturnSquareComposite.lean`](../MatrixMortality/ReturnSquareComposite.lean). The focused module
build passed. Namespace lint found no errors in 20 declarations under all 14 default linters.
The transitive axiom set is exactly `[propext, Classical.choice, Quot.sound]`. LSP diagnostics,
the forbidden-aperture scan, and `git diff --check` are clean.

```text
MASTER VERDICT: total divisibility is insufficient
REMOVED: resonance-only classification for arbitrary divisibility-chain scale alphabets
SURVIVES: arbitrary-composite ReturnSquare over the exact geometric scales qⁿ
```
