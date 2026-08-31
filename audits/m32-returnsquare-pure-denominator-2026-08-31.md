# M₃(2) ReturnSquare Pure-Denominator Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S51` makes every positive-numerator branch finite, but does not bound the tail for a pure
fraction `1/B`. This audit keeps the integral common-base adjugate recurrence and attacks its
denominator primes directly.

## Integral Leading Terms

For `tail=first::rest`, set `e=first+1`, `E′=waitExponent(rest)`, and `E=e+E′`. If

```text
(R,S)=J_tail·(B,1),
```

induction on the tail gives integers `u,v` such that

```text
S   = (−1)^|tail| q^(2E)  + B u,
R/B = (−1)^|tail| q^(2E′) + B v.                         (1)
```

The proof is integral; the correction terms need not be units and no common content is
discarded.

## Deep-Prime Certificate

Let `r=vₚ(q)>0` and `a=vₚ(B)`. Under the strict depth condition `2Er<a`, the leading terms in
(1) have smaller valuation than their `B`-multiples. Therefore

```text
vₚ(S)=2Er,                 vₚ(R/B)=2E′r.
```

If `R=qʰS`, comparison gives

```text
a=(h+2e)r,                 2E′<h.                         (2)
```

The physical bridge has `h=head+1`. For fixed `q,B`, equation (2) leaves finitely many choices
of `head` and `first`, then bounds `waitExponent(rest)`; the deep chamber is decidable by finite
exact adjugate enumeration. Applying (2) at two deep primes gives the additional obstruction

```text
vₚ(B) v_ℓ(q) = v_ℓ(B) vₚ(q).
```

Unequal normalized denominator depths kill the jointly deep branch before word evaluation.

## Scope

The theorem requires integral `q,B`, positive `vₚ(q)`, and strict `2Er<a`. The physical bridge
requires `B≠0`; nonzeroness of `q,B` is carried by their exact valuation hypotheses, while the
deep hypothesis forces `B≠1`. No reducedness assumption is used. The complementary chamber
`a≤2Er` remains open, including the critical equality where the two terms in (1) may cancel.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| pure-denominator tails are wholly unbounded | rejected | every deep-prime chamber is finite |
| the source exponent remains independent of denominator depth | rejected | equation (2) synchronizes them exactly |
| common-content cancellation invalidates the certificate | rejected | the recurrence and leading terms are integral |
| arbitrary-composite ReturnSquare is classified | open | simultaneously shallow denominator primes remain |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every deep pure-denominator prime yields a finite exact tail certificate

EXACT THROAT: classify the simultaneously shallow chamber `a≤2Er`

## Evidence

The formal owner is
[`ReturnSquarePureDenominator.lean`](../MatrixMortality/ReturnSquarePureDenominator.lean). The
focused module build, umbrella build, default namespace linters, transitive axiom inspection,
Lean LSP diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded
commit.
