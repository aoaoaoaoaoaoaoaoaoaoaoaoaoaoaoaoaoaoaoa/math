# M₃(2) Cubic Binary-Pump Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S65` found unary non-scalar stabilizers of nonaccepting source rays. A finite quotient might
still absorb one loop counter. The decisive next test is whether one safe ray already carries
branching stabilizer syntax and therefore exponentially many first-hit bridge spellings.

## Binary Loops

Lean checks

```text
C₀=[1,15,7,1],    Π(C₀)(4,3)=777600000(4,3),
C₁=[1,15,38,6],   Π(C₁)(4,3)=182891520000(4,3).
```

Both scales are nonzero, both words contain only positive waits, and neither product equals
`λI` for any rational `λ`. Concatenating the block selected by each bit defines a literal monoid
code `E`. Lean proves `E(βγ)=E(β)++E(γ)`, length `4|β|`, positivity, exact ray scale equal to the
product of the letter scales, and injectivity of `E`.

## First-Hit Family

With `S=[15,29,11,13,7,8]`, define

```text
W(β)=[13] ++ E(β) ++ S.
```

Lean proves

```text
Π(W(β))c=29617088832000000·∏ᵢ scale(βᵢ)·e₀,
M₀Π(W(β))M₀=0,
length(W(β))=7+4|β|.
```

The accepting scale is nonzero, every wait is positive, and the bridge constructor is injective
on arbitrary bit strings.

The first-hit property is uniform. Each loop block is suffix-safe from `(4,3)`, the fixed suffix
is suffix-safe from `c`, and a generic append theorem composes safe paths whenever the right word
lands nontrivially on the left source ray. Induction proves every proper suffix of every `W(β)`
has nonzero separator incidence. Only the complete word reaches acceptance.

For width `n`, the finite image indexed by `Fin n → Bool` has cardinality exactly `2^n`. Every
member has common length `7+4n`; every pair collides projectively at the accepting source image
with a nonzero explicit ratio.

## Adjudication

| Claim | Judgment |
| --- | --- |
| both loop ray actions and scales hold | Lean checked |
| both loops are positive and non-scalar | Lean checked |
| literal binary encoding is a concatenation morphism and injective | Lean checked |
| every encoded body preserves `(4,3)` with nonzero scale | Lean checked |
| every bridge word is positive, accepting, and an exact zero witness | Lean checked |
| every proper source-reading suffix is nonaccepting | Lean checked |
| fixed width `n` gives exactly `2^n` distinct common-length words | Lean checked |
| every fixed-width pair collides projectively on the accepting ray | Lean checked |
| the loop matrix products form a free projective semigroup | open in this result |
| a finite stabilizer quotient is impossible | not claimed |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: an exact free literal binary language of uniformly first-hit positive bridges
KILLED: any claim that the safe accepting language has only unary stabilizer branching
EXPOSED: whether full loop products retain the hidden bit stack transversely
NEXT: triangularize the loop products and test projective semigroup freeness
```
