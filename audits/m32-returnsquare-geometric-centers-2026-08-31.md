# M₃(2) ReturnSquare Geometric-Center Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The four exact inverse-wall laws admit nonresonant zeros for arbitrary scales. This audit uses
the sole surviving constraint: every scale is a positive power of one base `q`.

## Denominator Center

At the exact denominator center `st=B`, the inverse branch is `B/t²`. If the target is
`B/qⁿ`, the center condition forces `t=qⁿ` and the next state is `B/q²ⁿ`. Iteration forces

```text
scale exponents: n,2n,4n,…,
state exponent after k centers: 2ᵏn.
```

If this chain reaches the physical reverse endpoint `Aqʰ`, cross multiplication gives
`B=Aq^(h+2ᵏn)`. The parameter `A/B` is therefore a reciprocal power of `q`, already killed by
one return.

## Critical Center

At scale `qⁿ`, the zero critical residue clears to

```text
(B−A)(qⁿ)²−B=0.
```

In any prime quotient with `q=1`, this equation forces `A=0`. Fractional fixed-ray mortality
forces `B=A` in the same quotient. Hence both vanish, contradicting the explicit reduced-modulo-
`ℓ` hypothesis. Canonical coprime numerator-denominator pairs satisfy that hypothesis.

## Exact Search

An exact projective meet-in-the-middle search found no nonresonant common-base zero for
`q∈{6,10,12,18,30}`, word length at most fourteen, scale exponents at most five, synchronized
numerator exponent at most ten, and denominator-prime exponents at most twenty-four, after the
`R32-S48` filters. This is reconnaissance, not theorem evidence.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| consecutive exact denominator centers admit unit freedom | rejected | every transition doubles the exponent |
| a center-only suffix can end nonresonantly | rejected | its endpoint equation is a reciprocal base power |
| a mortal reduced fraction can have zero critical residue | rejected on every fixed-ray quotient | residue and mortality force both fraction coordinates to vanish |
| nonzero critical residues are classified | open | their normalized units can leave and re-enter valuation walls |
| arbitrary-composite ReturnSquare is classified | open | mixed nonzero residue cycles remain |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every nonresonant common-base zero must leave each denominator-center chain through a
nonzero normalized residue

EXACT THROAT: classify mixed nonzero-residue transitions or produce a common-base cycle

## Evidence

The formal owner is
[`ReturnSquareGeometricCenter.lean`](../MatrixMortality/ReturnSquareGeometricCenter.lean).
The focused module build, umbrella build, default namespace linters, transitive axiom inspection,
Lean LSP diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
