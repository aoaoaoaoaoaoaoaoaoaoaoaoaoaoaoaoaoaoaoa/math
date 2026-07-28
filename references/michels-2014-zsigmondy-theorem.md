# Bart Michels (2014): Zsigmondy’s Theorem

**Citation.** Bart Michels, “Zsigmondy’s Theorem,” revised December 1, 2014.

- Work identity: author exposition; no DOI or arXiv identifier
- Canonical source: https://bartmichels.github.io/files/zsigmondy_en.pdf
- Local artifact: `michels-2014-zsigmondy-theorem.pdf`
- Version and status: revised author-hosted exposition, December 1, 2014; not peer reviewed
- Retrieved: 2026-07-28
- SHA-256: `a6842c21fafea4aeaee265f07af3fec9aff895cb80c152d7525d7d2f2b5a36f3`
- Access and retention: publicly distributed from the author’s website; no explicit license located
- Synopsis basis: full-text inspection of the six-page PDF

## Synopsis

The note gives an elementary proof of Zsigmondy’s theorem. For coprime positive integers
`a > b` and `n > 1`, `aⁿ − bⁿ` has a prime divisor absent from every `aᵏ − bᵏ` with
`1 ≤ k < n`, except for `2⁶ − 1⁶` and the case `n = 2` with `a + b` a power of two.

Section 1 collects the required cyclotomic identities, the order of roots of cyclotomic
polynomials modulo a prime, a lifting-the-exponent lemma, and the bound

```text
(x − 1)^φ(n) ≤ Φₙ(x) < (x + 1)^φ(n)
```

for `x > 1`. Section 2 writes the homogeneous cyclotomic factor of `aⁿ − bⁿ` as the product
of its primitive part and a residual factor. It proves that the residual is either one or the
largest prime divisor of `n`, with exponent one for `n > 2`. The cyclotomic lower bound then
forces a nontrivial primitive part except in the two stated cases. The final section derives
the corresponding theorem for sums of powers and gives elementary applications.

## Source Assessment

The statement is classical, and the note identifies its proof as a reformulation of
Birkhoff–Vandiver. It delegates proofs of several prerequisites to cited sources, including
lifting the exponent and basic cyclotomic facts. No defect was found in the inspected argument,
but the artifact is an expository author note rather than the original or a peer-reviewed
edition.

## Project Use

The formal corpus reconstructs the `b=1`, `n>2` theorem from mathlib's cyclotomic and
lifting-the-exponent infrastructure, for every base greater than one. Primitive divisors supply
the finite quotient walls in the prime-power `ReturnSquare` classification. Exponent two and
the exceptional pair `(a,n)=(2,6)` use separate, explicit quotient certificates.
