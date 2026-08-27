# M₄(3) spectral-checksum obstruction audit

**Date:** 11 August 2026

**Status:** one-complement checksum architecture closed; nonlinear resonant incidence open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** add a syntax checksum to the unused one-dimensional complement of the original
parabolic cube root without losing the paired-data action

## Verdict

The complete rational one-complement family has an exact dichotomy. Requiring the indispensable
cube identity `Ŝ³J=TJ` forces either

```text
q=1,   z=2/3,   x,y arbitrary,
```

or

```text
q≠1,   x=y=0,   z=(1+q³)/(q²+q+1).
```

The nonresonant branch does carry the proposed exponential gap checksum, but the cube equations
remove both couplings that create the parabolic wall. Every reduced gap atom is then invertible,
and a rank factorization proves that every nonempty word in the three physical generators is
nonzero. In the resonant branch the complete gaps lie on the affine erase--rule line and contain
the already formalized gap-thirty pseudo-production, indeed an infinite ladder of exact aliases.

Thus syntax cannot be placed in this spare rational eigenvalue: `q≠1` makes the family immortal,
while `q=1` restores the pseudo-terminal obstruction. This closes the one-complement spectral
architecture, not all rational cube roots or all nonlinear consecutive-wall incidences.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`2e06706c872a14fb9a02246a16709314561c741e`. Its final-report SHA-256 digest is
`8ac1dbb5a75998ed063fc7af0c2f3e26b713d568226c6318008c281f5fe17404`.

The algebraic classification, determinant formulae, rational nonvanishing arguments, and
arbitrary-word factorization below were independently reconstructed. The report's broader claim
that every separate linear history state must accept all affine pseudo-gaps is not retained; its
interpolation lemma is correct, but the proposed application silently assumes that forward
completeness accepts every Boolean assignment to a fixed tile skeleton.

## Root Classification

In the paired basis put

```text
C = [[0,-1],[1,-1]],     A=diag(C,1),
Ŝ = [[A,0],[v,q]],       v=(x,y,z).
```

Since `C³=I`, block multiplication gives

```text
Ŝ³ = [[I₃,0],[vP_q,q³]],
P_q = A²+qA+q²I
    = [[q²-1, 1-q, 0],
       [q-1, q(q-1), 0],
       [0, 0, q²+q+1]].
```

The common-image injection has final column `e₃-e₄`, so `Ŝ³J=TJ` is equivalent to

```text
vP_q=(0,0,1+q³).
```

The determinant of the upper block of `P_q` is
`(q-1)²(q²+q+1)`. The last factor has no rational root, yielding exactly the two branches in the
verdict.

## Semisimple Immortality

For `q≠1`, define the reduced gap atoms `Q_x(g)=F_xŜ^gJ`. The final column of `Ŝ^gJ` is
`e₃+h_g e₄`, where

```text
h_g=(1+q³-2q^g)/(1-q³).
```

Writing `ρ=3^β` and letting `M=3^n`, where the relevant `c`-rule lower word has length
`n≥4`, direct expansion gives

```text
det Q_b(g) = 27ρ (9-q³-8q^g)/(1-q³),
det Q_c(g) = 3 (M-3q³-(M-3)q^g)/(1-q³).
```

Both numerators are nonzero for rational `q≠1`. For nonnegative `q`, monotonicity makes `q=1`
the unique root. For negative `q`, odd gaps have the wrong sign. Writing `-q=a/b` in lowest
terms for even gaps, denominator clearing and coprimality force `a` to be a power of `3`; the
remaining valuation equations reduce either to `b(a-b)=1` with `a` a power of `3`, or to a
strict size contradiction. The same argument handles the isolated gap-two cases. Hence every
`Q_b(g)` and `Q_c(g)` is invertible.

An arbitrary physical word containing data letters factors as

```text
(Ŝ^a₀J) Q_x₁(a₁) ... Q_xₖ₋₁(aₖ₋₁) (F_xₖŜ^aₖ).
```

The left factor has full column rank, the middle is invertible, and the right factor has full
row rank because its product with `J` is an invertible gap atom. The product has rank three.
A pure root word is nonzero because its upper `3 × 3` block is `A^m`. This proves immortality
for every word, including empty gaps and malformed placements.

## Resonant Alias Ladder

For `q=1`, the cube is `D=I+2E₄₃`, so `D^j=(1-j)I+jD`. Every complete gap therefore satisfies

```text
Q_x(3j)=(1-j)Q_x(0)+jQ_x(3).
```

For the `b` role this is the side-normal pair

```text
10^β1 / word(j),
code(word(j))=1+24j,   3^|word(j)|=3+24j.
```

At `j_k=(9^k-1)/8`, the lower word is exactly `1^(2k)0`. Thus gaps `0`, `3`, and `30` give
respectively the intended erase, intended rule, and first poison `11110`; larger `k` give an
infinite pseudo-production ladder. The gap-thirty member and its nonhalting 33-tile witness are
already formalized by `M4-O15`.

## Rejected Generalization

For affine operators `A_i(t)=(1-t)A_i(0)+tA_i(1)`, multilinearity does express a product at
arbitrary parameters as a linear combination of its Boolean-corner products. Consequently a
linear accepting subspace containing all Boolean corners also contains every affine
extrapolation.

This conditional lemma does not by itself obstruct a chronology certificate. A sound compiler
may accept only the Boolean assignments that encode lawful histories, not every assignment on a
fixed skeleton. No generic prohibition on scalar checksums, invariant subspaces, or linear
history states is therefore entered in the salvage registry.

## Master Consequence

Delete the entire rational one-complement spectral-checksum family. The original parabolic lane
now needs a nonlinear legality invariant inseparable from the wall incidence, a narrower source
whose lawful image excludes every affine alias, or a genuinely different root family. The
all-word projective-orbit node remains independent.
