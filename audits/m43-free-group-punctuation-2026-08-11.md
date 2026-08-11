# M₄(3) free-group punctuation audit

**Date:** 11 August 2026

**Status:** four-dimensional punctuation closed; positive binary source compiler open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** turn Carvalho's free-cancellation simulation into mortality of three integer
`4 × 4` matrices

## Verdict

The report does not settle `M₄(3)`, but it establishes a second coherent trunk independent of
the parabolic family.

First, fixed universality does not make Carvalho's closed-path subgroup small. For the exact
repository source its rank is `648b+7≥655`, where `b` is the cardinality of the fixed binary
interpreter state type. More strongly, the equalizer is trivial on nonhalting instances and
infinite cyclic on halting instances. An explicit character shows that its nontrivial element is
missed by the positive monoid on every generator of the natural all-positive Nielsen basis.
The naive “use a positive closed-path basis” route is therefore closed even if all 655 or more
generators are retained.

Second, free-group equality with a fixed boundary mismatch has an exact homogeneous
four-dimensional mortality compiler. Two binary data letters act by the integral left--right
representation on `M₂(ℤ)`, and one boundary-bearing rank-one separator punctuates them. Lean
checks the representation coefficient, composition, unimodularity, and the generic
arbitrary-word boundary punctuation theorem. Ping-pong and a rational-eigenline argument prove
that the coefficient vanishes exactly at free-group equality.

The remaining seam is exact:

```text
∃ τ∈{0,1,H,p}*, n≥0: τ p H^n = d_e Ψ(τ)
  ↔
∃ w∈{0,1}*: α_e(L_e w R_e)=β_e(L_e w R_e),
```

with `α_e(L_eR_e)≠β_e(L_eR_e)`. A compiler with a converse over every positive binary word
would immediately prove `M₄(3)` undecidable. No such compiler is supplied.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`2e06706c872a14fb9a02246a16709314561c741e`. Its final-report SHA-256 digest is
`7ef152cc4f1ce7a2cc6f745aa28d4ba02cf6b127f2b4d50ce033b7b39128df06`.

The transducer calculation and strengthened fixed-subgroup theorem were checked against
Carvalho's arXiv v2, retained as
[`carvalho-2026-free-group-pcp.pdf`](../references/carvalho-2026-free-group-pcp.pdf). The
four-dimensional algebra and arbitrary-word separator proof were reconstructed independently;
their formal spine is retained in `SchottkyPunctuation.lean` and `TerminalTile.lean`.

## Fixed Source Rank

Let `b` be the cardinality of
`UniversalTwoTag.Construction.BinaryState`. The repository definitions give:

```text
BinaryState = Unit ⊕ supported interpreter labels,               so b≥1;
ReadState   = (normal | restore) × BinaryState × Bool,            so |ReadState|=4b;
CockeMinsky.Symbol has 27 state-indexed constructors plus halt,   so q=108b+1;
CyclicTag.ofTwoTag appends q production phases and q empty phases, so m=216b+2.
```

Carvalho's numbered transducer has input alphabet `B={0,1,H,p}`. Its state displacement is the
homomorphism

```text
ν:F(B)→ℤ/m,   ν(0)=ν(1)=1,   ν(H)=ν(p)=0.
```

Hence the loop-label subgroup is `H_m=ker ν`, of index `m` in `F₄`. Nielsen--Schreier gives

```text
rank H_m = 1+m(4-1)=3m+1=648b+7≥655.
```

An exact positive Nielsen basis is

```text
z=0^m,
X_i=0^i 1 0^(m-i-1),
Y_i=0^i H 0^(m-i),
Z_i=0^i p 0^(m-i),                 0≤i<m.
```

It is obtained from the standard Schreier basis by multiplying generators on the right by
`z`, so it remains a free basis.

## Cyclic Fixed Subgroup

Carvalho's discrepancy proof classifies a reduced fixed loop into a positive prefix followed by
a negative suffix. Both halves, after reversing the latter, are initial segments of the unique
orbit obtained by repeatedly reading the first discrepancy letter. Thus every fixed loop is the
difference of two prefixes ending at the same discrepancy-state pair.

Proposition 3.2 proves that this orbit has no repetition before halting. After halting it reaches
a marker-only word `D∈{H,p}+` containing exactly one `p`; reading it rotates the word. The
rotations are distinct because such a word is primitive. If `τ` is the prefix entering this
cycle, all repeated-prefix differences are powers of `τDτ⁻¹`. Therefore

```text
Fix(θ_e) = {1}                         if e does not halt,
Fix(θ_e) = ⟨τDτ⁻¹⟩                    if e halts.
```

This sharpens Carvalho's nontriviality statement for the pinned transducer without changing
the paper's reduction.

Define the binary-exponent character

```text
σ(0)=σ(1)=1,   σ(H)=σ(p)=0.
```

Every fixed element has character zero because `D` is marker-only. Every generator of the
positive Nielsen basis has character `m`. Hence every nonempty positive basis word has positive
character and

```text
Eq(g_e,h_e) ∩ (positive Nielsen basis)* = {1}.
```

This is the exact obstruction `M4-O17`.

## Positive Transducer Equation

Rotate the terminal marker word until its unique `p` is first, writing `D=pH^n`. If `Ψ(τ)` is
the output of the fixed numbered transducer on positive input `τ` and `d_e=w_ep`, the halting
condition becomes

```text
∃τ,n: τ p H^n=d_e Ψ(τ).
```

The converse is all-path sound. Both sides are positive and the discrepancy retains its unique
`p`; equality forces the first input letter to equal the first discrepancy letter. Cancelling
and iterating reconstructs the deterministic first-letter path, and the marker-only terminal
discrepancy certifies that the cyclic-tag queue is empty.

## Homogeneous Equality Detector

Put

```text
S=[[10,3],[3,1]],   T=[[10,-3],[-3,1]].
```

Four disjoint real intervals give the standard ping-pong inclusions for `S,T` and their
inverses. They freely generate a purely hyperbolic subgroup of `SL₂(ℤ)`. For `A,B∈SL₂(ℤ)`, let

```text
Λ(A,B)=B^(-T)⊗A
```

act on the four-dimensional lattice `M₂(ℤ)`. With `c₀=vec(E₁₂)` and `λ=trace`, Lean proves

```text
λ Λ(A,B)c₀ = A₁₀B₀₀-A₀₀B₁₀ = -det(Ae₁,Be₁).
```

On the explicit Schottky subgroup this vanishes exactly when `A=B`. Indeed, vanishing gives a
rational eigenline for `B⁻¹A`; its rational integral unit eigenvalue is `±1`, hence its trace is
`±2`. Pure hyperbolicity excludes every nonidentity element with that trace.

## Boundary Punctuation

Let binary homomorphisms `α,β` into the Schottky free group give data matrices
`D_i=Λ(ρ(α(i)),ρ(β(i)))`. Fix binary boundaries `L,R` with
`α(LR)≠β(LR)`, and set

```text
q=D_R c₀,   r=λD_L,   Π=q r.
```

The new generic Lean theorem folds `L` and `R` into the two separator rays and proves

```text
{D₀,D₁,Π} mortal
  ↔ ∃w: λD_(LwR)c₀=0
  ↔ ∃w: α(LwR)=β(LwR).
```

Its converse quantifies over every physical word. A word without `Π` is invertible; one `Π` is
a nonzero outer product; two or more copies vanish exactly when one intervening data block has
zero coefficient. The boundary mismatch makes `Π²≠0`, so empty blocks and punctuation runs do
not create false zeros.

## Literature Boundary

[`Logan`](../references/logan-2022-equalizer-rank-two.md) proves that an equalizer from `F₂` has
rank at most two when one map is injective, but his general theorem is structural rather than an
algorithm for triviality. His basis algorithm needs retract-image hypotheses.
[`Ciobanu--Logan`](../references/ciobanu-logan-2021-free-group-pcp-variations.md) relate
free-group GPCP to PCP under injectivity, rational, or conjugacy conditions, with a
two-source-generator overhead; they do not eliminate arbitrary boundaries for a positive binary
source. Myasnikov--Nikolaev--Ushakov prove group GPCP undecidability with unbounded presentation
data and signed words. Carvalho proves unrestricted free-group PCP undecidable, but the pinned
construction has the high domain rank computed above.

Thus the surviving binary positive fixed-boundary equation is adjacent to a genuine fixed-rank
algorithmic boundary. It must be attacked in both directions: construct the compiler, or prove
that this restricted equation is decidable or cannot carry Carvalho's source.

## Master Consequence

The fifth affine coordinate is no longer an obstruction. If the binary fixed-boundary compiler
exists, the formal boundary separator immediately produces three integer `4 × 4` matrices with
a complete arbitrary-word converse. If the restricted equation is decidable, this entire
free-cancellation trunk is dead and must be pruned. Either outcome cuts directly at `M₄(3)`.
