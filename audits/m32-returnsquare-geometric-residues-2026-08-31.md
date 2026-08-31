# M₃(2) ReturnSquare Geometric-Residue Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S49` excludes center-only chains and the zero critical residue. This audit tests the first
exit-and-re-entry pattern: the zero equal-scale residue followed by an exact denominator center.

## Transition

At scale `t`, the zero equal-scale residue is `u=A−B`. Its exact predecessor is

```text
A−t²(A−B).
```

If scale `r` makes this state a denominator center, clearing the equality gives

```text
(rt²−1)B = r(t²−1)A.                                      (1)
```

Lean proves (1) equivalent to the original rational inverse transition; no primitive gcd or
affine denominator is omitted.

## Signed Quotient

Let `q=−1` in `ZMod ℓ`, with `ℓ` odd. Every `t=qᵐ` satisfies `t²=1`. For an odd center exponent,
`r=qⁿ=−1`, and (1) reduces to `2B=0`. Thus `B=0`. If the original fraction is mortal,
`R32-S48` gives `B=±A`, so `A=0`, contradicting reducedness modulo `ℓ`.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| the zero equal-scale residue can re-enter at any exponent | rejected in odd signed quotients | odd exponents force both fraction coordinates to vanish |
| even center exponents are excluded by the same quotient | rejected | `r=1` makes (1) tautological after `t²=1` |
| nonzero equal-scale residues are classified | open | their unit survives the signed reduction |
| arbitrary-composite ReturnSquare is classified | open | even and mixed nonzero-residue re-entry remains |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: a zero equal-scale residue has even immediate center exponent whenever `q+1` supplies
an odd reduced signed-ray prime

EXACT THROAT: kill the even re-entry class with higher-order cyclotomic quotients or derive its
exact power resonance

## Evidence

The formal owner is
[`ReturnSquareGeometricResidue.lean`](../MatrixMortality/ReturnSquareGeometricResidue.lean).
The focused module build, umbrella build, default namespace linters, transitive axiom inspection,
Lean LSP diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
