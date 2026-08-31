# M₃(2) ReturnSquare Fractional Finite-Wall Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The prime-power ReturnSquare classification uses finite quotients only after rational-root
support reduces the parameter to `d=1/D`. Composite bases permit reduced fractions `A/B` with
different base primes on the two sides. The audit tests whether the same cyclotomic rays survive
without the assumption `A=1`.

## Cleared Fraction

For `B≠0`, the integer cut

```text
C_{A,B} = [−B   B   B−A]
          [−A   B     0]
          [−B   B   B−A]
```

casts to `B·cut(−A/B)`. Scaling the cut generator by nonzero `B` preserves zero products, so
Lean proves exact mortality equivalence between the cleared integer pair and the rational pair.

## Fixed Ray

If `q=1` in `ZMod ℓ`, both the ambient generator and the cleared cut preserve
`(1,1,1)`. Their weights are `1` and `B−A`. For prime `ℓ`, a nonzero common-eigenvector wall
therefore proves

```text
mortality  ⇒  B≡A (mod ℓ).                                  (1)
```

In particular, every prime divisor of `q−1` divides `B−A`.

## Signed Rays

If `q=−1`, the ambient generator exchanges `(1,1,1)` and `(1,−1,1)`. The cut resets both to
`(1,1,1)`, with respective weights `B−A` and `−(B+A)`. The exact two-state ray action gives

```text
mortality  ⇒  B≡A or B≡−A (mod ℓ).                          (2)
```

Thus every prime divisor of `q+1` divides `B−A` or `B+A`.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| clearing a general fraction preserves mortality | promoted | generator-wise nonzero scaling equivalence checked |
| the fixed ray requires `A=1` | rejected | its general cut weight is exactly `B−A` |
| the signed two-ray automaton requires `A=1` | rejected | its cut weights generalize to `B−A` and `−(B+A)` |
| every mortal fraction obeys (1)–(2) | promoted | finite-field ray walls and integer congruence corollaries checked |
| order-one and order-two quotients classify all fractions | rejected | their simultaneous congruence lattice contains non-power assignments |
| arbitrary-composite ReturnSquare is classified | open | higher-order quotient automata and common-geometric residue cycles remain |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every candidate fraction must lie on the signed identity rays modulo all prime factors
of `q−1` and `q+1`

EXACT THROAT: classify higher-order ambient projective automata or prove that the four-wall
geometric residue cycle violates one of the signed cyclotomic conditions

## Evidence

The formal owner is
[`ReturnSquareFractionFiniteWall.lean`](../MatrixMortality/ReturnSquareFractionFiniteWall.lean).
The focused module build, umbrella build, default namespace linters, transitive axiom inspection,
Lean LSP diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
